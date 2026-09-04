# Negative knowledge

Project-wide index of recorded laboratory failures. Search this page
before opening a branch. Do not re-test a discarded hypothesis unless
new mathematics changes the situation.

This page is an inventory, not a theorem. Finite checks are not proofs.
The index does **not** say that every compression fails, that no
nontrivial cycle exists, or that Collatz or Juggler is solved.

The four homes remain: `conjectures/refuted/`, `REFUTED` rows in
[theory/theorem_ledger.md](theory/theorem_ledger.md), journal
**Refuted ideas**, and dossier **Counterexamples**. This page is the
lookup. Juggler paper-cut companions:
[juggler_branch_ledger.md](juggler_branch_ledger.md),
[theory/juggler_cycle_itinerary_structure_note.md](theory/juggler_cycle_itinerary_structure_note.md)
§8.

## Kinds

| Kind | Meaning |
|---|---|
| `REFUTED` | A named hypothesis has a counterexample or a dominance proof |
| `REPARAMETERIZATION` / `KNOWN` | The attack is an existing identity under a new name |
| `METHOD_OBSTRUCTION` | The toolkit dies; the mathematical question may remain open |
| `PARK_STOP` | Payoff too low or blocked; not a kill |

Exclude from this page as failures: PROMOTE theorems, active
conjectures, and the still-open densities \(57/64\) and \(29/32\)
(`CONJECTURE`). Journal **Refuted ideas** lines are pointers into the
same identifiers; they are not a third unique source.

Each cluster names the killed claim, the kill, what not to reopen, and
the source identifiers. The [source inventory](#source-inventory) lists
every required id so a later `REFUTED` row cannot hide.

---

## BT operators and rewrite

Standing methodology examples live here: sample minimization is not
exact Myhill–Nerode minimization; naive recursive reduction of \(x^3\)
fails; \(Q\) admits no bounded residue / valuation / \(B_t\) classifier;
nonzero cross-depth overlap is not exhausted by the zero spine;
valuations do not determine 3-adic lifting behaviour.

### Operators

Killed claim: \(W\) is an involution; \(W(3n)=3W(n)\); \(W\) commutes
with accelerated \(T\); \(S\circ D=\mathrm{id}\); \(D\) is floor-division.
Kill: \(W(3)=1\) and \(W(W(3))=1\neq 3\); \(W(3)\neq 3W(1)\);
\(W(T(3))\neq T(W(3))\); \(S\circ D\) fails on \(\mathbb Z\);
\(D(2)=1\neq\lfloor 2/3\rfloor\).
Kind: `REFUTED`.
Do not reopen: BT warp as a conjugacy; reversal as a Collatz intertwiner.
Witness: \(n=3\) (involution, commute); \(n=1\) for \(W(3n)\).
Pinned: [tests/regression/test_counterexamples.py](../tests/regression/test_counterexamples.py).

Members: `BT-W-not-involution`, `W_not_involution`, `W_three_n`,
`W_commutes_T`, `W_R_reverse_itinerary`, `S_circ_D_id`.

### Rewrite confluence and semantic NF

Killed claim: a small operator-fragment or word table is locally
confluent / a unique semantic representative.
Kill: distinct irreducibles agree under `evaluate`; unary plus push-in
\(S\) through Add/Mul is not LC; \(N\)-through-Add is not a semantic
NF; factor-out Add (binary or AC) is not semantically complete;
one-way \(N\circ D\) plus stock \(W/K_3\) or SIMP is not LC.
Kind: `REFUTED`.
Do not reopen: tree-rule NF as integer-operator uniqueness.

Members: `BTC-op-fragment-semantic-nf`, `op_fragment_semantic_nf`,
`BTC-add-s-push-lc`, `add_s_push_lc`, `BTC-mul-s-push-lc`,
`mul_s_push_lc`, `BTC-add-n-push-semantic`, `add_n_push_semantic`,
`BTC-w-nd-word-lc`, `w_nd_word_lc`, `BTC-add-factor-binary-semantic`,
`add_factor_binary_semantic`, `BTC-add-factor-ac-semantic`,
`add_factor_ac_semantic`, `BTC-word-full-lc`, `word_full_lc`,
`BTC-word-simp-nd-lc`, `word_simp_nd_lc`.

---

## Collatz and dual code

Killed claim: unrestricted odd-part is one FST; \(\mathrm{BT}(R)\)
determines the next valuation or lift digit; \(n_*\le n\) on
contracting prefixes; \(H_{\mathrm{BT}}\) adds an exact obstruction
beyond code\(+R\); every expanding extension must lift; a one-step
Lyapunov kills shortcut Collatz.
Kill: odd-part is not a single rational transduction
(`C-odd-part-not-one-fst`, exact); same \(R=3\), \(\mathrm{BT}(R)=+0\),
different endpoints and lift digits; smallest \(n_*\le n\) failure
\(n=165\), \(m=17\); \(H_{\mathrm{BT}}\) independence fails; expanding
prefixes can stay zero-lift; shortcut one-step Lyapunov is false.
Kind: `REFUTED`.
Do not reopen: dual-code suffix as a next-lift classifier; \(n_*\le n\)
as a general finite-code inequality.

Members: `BT_R_suffix_determines_next_valuation`, `C-nstar-le-n`,
`n_star_le_n`, `H_BT_independence`, `expanding_extension_must_lift`,
`C-shortcut-one-step-lyapunov`.

CLOSE dossiers: [collatz](problems/collatz.md) (application PARK as a
whole; exact layer recorded),
[collatz_finite_descent](problems/collatz_finite_descent.md),
[weak_collatz_floor_5x4_rplus](problems/weak_collatz_floor_5x4_rplus.md).

---

## Residuals, Newton, \(Q\), lifting

Killed claim: LSD sample minimization equals Myhill–Nerode \(M_k\);
prefix locality implies a small automaton; Newton classes of \(x^3\)
are packed-prefix congruence classes; \(M_{k+1}=3M_k+1\);
\(N_2\Rightarrow N_1\Rightarrow N_0\); every collision is a sign pair;
deepest fibres are full residue classes; \(Q\) is an ordinary residual
with a bounded \(\Psi\) / \(B_t\) classifier; \(v_3(f)\) and \(v_3(f')\)
determine lifting; \(\Phi_r\) is a minimal state.
Kill: sample \(\neq M_k\); locality does not give a small automaton;
coefficientwise vanishing and \(\tau=1+\min v_3(c_j)\) fail;
the \(x^3\) prefix / lift / \(N_2+N_1\Rightarrow N_0\) / deep-coset /
intermediate-renormalization / deficit-2 / \(Q\)-visibility /
\(\Psi\)-inverse slogans all have named witnesses (including
\(\{720,738\}\) at \(k=8\)); valuations agree at the level-1 node \(0\)
of \(x^2\pm 9\) with six surviving grandchildren versus none;
\(\Phi_r(x)\neq\Phi_r(-x)\) with identical futures.
Kind: `REFUTED` / `REPARAMETERIZATION`.
Do not reopen: \(Q\) as a residue class; valuation-only lifting;
recursive copy of the deficit-\(r\) problem as the remaining locus.

Members: `BTA-coeffwise-nec`, `BTA-tau-minc`, `BTA-sample`,
`BTA-locality-small`, `BTA-x3-prefix`, `BTA-x3-lift`, `BTA-x3-n2n1`,
`BTA-x3-n21n0`, `BTA-x3-allsign`, `BTA-x3-deep-coset`,
`BTA-x3-inter-n21n0`, `BTA-x3-inter-eqprev`, `BTA-x3-inter-renorm`,
`BTA-x3-def2-n21n0`, `BTA-x3-def2-nextdigit`, `BTA-x3-n0-recur`,
`BTA-x3-Q-vis`, `BTA-x3-Q-inv-psi`, `BTL-valuations-insufficient`,
`BTL-phi-not-minimal`.

CLOSE / mixed dossiers: [residuals](problems/residuals.md)
(counting line CLOSE; structural PROMOTE),
[lifting](problems/lifting.md) (dossier PARK; multivariate /
minimal-state / unordered-shape CLOSE),
[stabilization](problems/stabilization.md),
[padic_dynamics](problems/padic_dynamics.md),
[prime_residual_complexity](problems/prime_residual_complexity.md)
(`PRC-jet-equals-prime`).

---

## Signed-digit residual, multiplicative residual, Ostrowski

Killed claim: a scalar / geometry / Mealy / merge / short-horizon /
factor-count classifier organizes signed-digit residual; expanding
magnitude / \(J_2\)-third / \(J_3=J_1\) / `lsd`-sum slogans hold;
Ostrowski zero-monoid is NP-complete in the claimed reading;
unnormalized mode is bounded; long words force infinite \(L_0\);
an extra terminal congruence remains.
Kill: named `BTN-sdr*`, `BTN-sdrm*`, `BTN-sdrc*`, `BTN-sdsh*`,
`BTN-mr*` counterexamples; expanding-magnitude and jet-third fail;
`D(\mathrm{lsd}\,x+\mathrm{lsd}\,y)\) is not the residual of the sum;
Ostrowski slogans die as `KNOWN` / false completeness.
Kind: `REFUTED` / `REPARAMETERIZATION`.
Do not reopen: a bounded Mealy for unbounded residual coefficients;
Ostrowski \(L_0\) emptiness by a new congruence.

Members: `BTN-expanding-magnitude`, `BTN-expanding-j2-third`,
`BTN-expanding-j3-j1`, `BTN-dadd-lsd-sum`, `BTN-sdr-scalar-lambda3`,
`BTN-sdr-geometry-phase`, `BTN-sdr-maxabs-mealy`,
`BTN-sdrg-lattice-all-U`, `BTN-sdrg-sign-mealy`,
`BTN-sdrm-merge-exists`, `BTN-sdrm-mod3-merges`,
`BTN-sdrc-need-constant`, `BTN-sdrc-residual-merge`,
`BTN-sdsh-short-separator`, `BTN-sdsh-only-deadlock`,
`BTN-sdsh-subset-merge`, `BTN-mr-factor-count`, `BTN-mr-three-states`,
`OST-np-complete-zero-monoid`, `OST-np-unnormalized-mode-bound`,
`OST-np-long-words-infinite-L0`, `OST-np-extra-terminal-congruence`.

CLOSE dossiers: [ostrowski_order_m_adder](problems/ostrowski_order_m_adder.md)
(\(L_0\) PARK; Myhill–Nerode / Hankel CLOSE),
[operator_dynamics](problems/operator_dynamics.md),
[operator_dynamics_benchmark](problems/operator_dynamics_benchmark.md).

---

## Juggler language, residual, and geometry

Killed claim: a proper residual / future / sum-\(\rho\) / information /
interval / PE-grammar / 4-letter certificate chain is a new forward
quotient; isolated exact floors or square seams move leftovers.
Kill: intrinsic future needs the current landing \(y\); listed
projections do not predict bounded residual futures; accumulated
remainders stay state-dependent; fixed-sample precision does not grow;
unary corridors are scale plus landing parity; realizable-language
factor closure survives with no extra PE grammar; iterating
\(\{E,OE,OOEE,R\}\) is a label on first descents; floor is a no-op iff
the state is a square; isolated seams are zero-defect cell junctions
(`*OO` / `*EE`).
Kind: `REFUTED` / `REPARAMETERIZATION`.
Do not reopen: residual-state sufficiency; certificate transitions as
a new dynamics; square-state cycle census.

Members: [juggler_residual_state](problems/juggler_residual_state.md),
[juggler_residual_minimize](problems/juggler_residual_minimize.md),
[juggler_future_quotient](problems/juggler_future_quotient.md),
[juggler_sum_rho](problems/juggler_sum_rho.md),
[juggler_information_complexity](problems/juggler_information_complexity.md),
[juggler_realization_geometry](problems/juggler_realization_geometry.md),
[juggler_word_language](problems/juggler_word_language.md),
[juggler_certificate_transitions](problems/juggler_certificate_transitions.md),
[juggler_first_return_excursions](problems/juggler_first_return_excursions.md),
[juggler_adversarial_paths](problems/juggler_adversarial_paths.md),
[juggler_exact_floor_impact](problems/juggler_exact_floor_impact.md),
[juggler_square_seam](problems/juggler_square_seam.md),
[juggler_backward_geometry](problems/juggler_backward_geometry.md),
[juggler_cell_hut](problems/juggler_cell_hut.md),
[juggler_preimage_cylinders](problems/juggler_preimage_cylinders.md),
[juggler_formal_realized_gap](problems/juggler_formal_realized_gap.md),
[juggler_anchor_cylinders](problems/juggler_anchor_cylinders.md),
[juggler_excursion_transfer](problems/juggler_excursion_transfer.md),
[juggler_survivor_phase](problems/juggler_survivor_phase.md),
[juggler_survival_set](problems/juggler_survival_set.md),
[juggler_accelerated](problems/juggler_accelerated.md),
[juggler_oo_descent_density](problems/juggler_oo_descent_density.md),
`J-two-block-persistent-expanding` (certified *counterexample* to forced
contraction after one block — a success that is a refutation),
`J-expansion-slack-uniform-tax`, `J-approx-equality-rigidity`,
`J-expanding-grammar-obstruction`, `J-landing-theta-state`,
`J-peak-transports-to-oo`, `J-pe-history-valuation`,
`J-pe-cylinder-next-landing`, `J-odd-landing-set-structure`,
`juggler_mixed_word_strictness`.

---

## Collision Factorization and local leftover-killers

Killed claim: a finite local configuration around a hypothetical cycle
is contradictory — a new seam, ancestry DAG, joint pair law, word-order
invariant, one-sided error transport, circuit drop \(T^L(t)<n\),
\(\xi\)-cocycle lift, or inverse-tube emptiness.
Kill: fibres are parity plus interval only (`even_preimage_iff`,
`odd_preimage_unique`, `preimage_same_next_state`). First meeting at
\(x\) iff the off-cycle parent \(t\) is off-cycle. Lift identity
\(T^L(t)=c\ge n\). Forced isolated-`OE` is false.
Kind: `REPARAMETERIZATION` / `REFUTED` slogans. **METHOD_OBSTRUCTION**
for any later “local configuration” attack.
Do not reopen: seam, ancestry, provenance, collision-pair, word-order,
error-transport, cycle-lift drop, inverse-width, odd-inverse
width/parity, mechanical lift, cyclic seam, seam sliding, seam
propagate, intersection taxonomy, \(E^r\) block.

Witness: \(100\to 10\leftarrow 102\); \(365/501\) at \(763\);
\(25\to 125\) Type 2; sink \(2\to 1\) fails the drop.

Members: [juggler_first_collision](problems/juggler_first_collision.md),
[juggler_cycle_first_collision](problems/juggler_cycle_first_collision.md),
[juggler_cycle_seam_ancestry](problems/juggler_cycle_seam_ancestry.md),
[juggler_cycle_cyclic_seam](problems/juggler_cycle_cyclic_seam.md),
[juggler_cycle_seam_sliding](problems/juggler_cycle_seam_sliding.md),
[juggler_cycle_seam_propagate](problems/juggler_cycle_seam_propagate.md),
[juggler_cycle_intersection_taxonomy](problems/juggler_cycle_intersection_taxonomy.md),
[juggler_cycle_e_block](problems/juggler_cycle_e_block.md),
[juggler_cycle_word_order](problems/juggler_cycle_word_order.md),
[juggler_cycle_error_transport](problems/juggler_cycle_error_transport.md),
[juggler_cycle_lift_ancestry](problems/juggler_cycle_lift_ancestry.md),
[juggler_cycle_mechanical_lift](problems/juggler_cycle_mechanical_lift.md),
[juggler_cycle_inverse_width](problems/juggler_cycle_inverse_width.md),
[juggler_odd_inverse_width](problems/juggler_odd_inverse_width.md),
[juggler_odd_inverse_parity](problems/juggler_odd_inverse_parity.md),
`juggler_first_collision`, `juggler_cycle_first_collision`,
`juggler_cycle_seam_ancestry`, `juggler_cycle_cyclic_seam`,
`juggler_cycle_seam_sliding`, `juggler_cycle_seam_propagate`,
`juggler_cycle_intersection_taxonomy`, `juggler_cycle_e_block`,
`juggler_cycle_word_order`, `juggler_cycle_itinerary_order`,
`juggler_cycle_error_transport`, `juggler_cycle_lift_ancestry`,
`juggler_mechanical_lift_obstruction`, `juggler_cycle_inverse_width`,
`juggler_odd_inverse_width`, `juggler_odd_inverse_parity`,
`juggler_cycle_itinerary_functional_closure`,
[juggler_functional_graph_seam](problems/juggler_functional_graph_seam.md),
[juggler_cycle_arrival_collision](problems/juggler_cycle_arrival_collision.md).
Lean packaging of Collision Factorization (`Seam.lean`,
`CyclePosition.lean`) is this kill under integer-edge and
predecessor-type names, not a new local attack.

---

## Corridor, PE, cube, and escape slogans

Killed claim: a later leftover corridor (first OO surplus, OOEOOE
FiniteProgress, inevitable OOO, post-OOO drop, second-OO acyclicity,
oneshot re-entry, third-residual PE, escaped-even drop, post-\(L\)
re-entry, \(W_5\) hierarchy, parity-persist budget, episode dichotomy,
empty-odd PE forward, PE intersection, PE-walk Lyapunov, odd-run
grammar, \(Q\)-state, cube-even progress, source descent, mixed-OE
defect, first-eighth, \(Q\)-return section) excludes a cycle or forces
FiniteProgress.
Kill: each slogan has a named witness on the leftover controls
\(365\), \(501\), \(1517\), \(6187\) (and \(37\), \(89\), \(193\),
\(4309\), …). The surviving exact facts are cells, envelope
\(x^A\le n^B\), and Collision Factorization. Local envelope ladders
are not new itinerary families.
Kind: `REFUTED`.
Do not reopen: post-\(L\) escape corridor cluster; cube-not-square as a
cycle-word family; landing-\(\theta\); iterated odd-landing sets.

Members: `J-cyclemin-necklace`, `J-cyclemin-bunched-short-path`,
`J-cyclemin-front-oo-raise`, `J-cyclemin-short-even-not-square`,
`J-cyclemin-short-defect-obstruction`, `J-cyclemin-first-oo-surplus`,
`J-cyclemin-ooeooe-finite-progress`,
`J-cyclemin-ooeooe-next-o-always-drop`, `J-cyclemin-ooo-inevitable`,
`J-cyclemin-post-ooo-always-drop`, `J-cyclemin-odd-oooe-even-q-drops`,
`J-cyclemin-second-oo-scale-acyclic`,
`J-cyclemin-scale-loop-signature-repeats`, `J-cyclemin-oneshot-reenters`,
`J-third-residual-drop-or-pe`, `J-escaped-even-always-drops`,
`J-cyclemin-post-l-ooe-reenters-l`, `J-oe-next-escaped-even`,
`J-cyclemin-second-post-l-ooe-oe-drops`, `J-second-o-below-square`,
`J-cyclemin-k5-post-l-hierarchy`, `J-cyclemin-odd-k5-generic`,
`J-cyclemin-w5-second-oo-u-fifth`, `J-cyclemin-odd-u-generic`,
`J-cyclemin-parity-persist-budget`, `J-cyclemin-l-odd-run-envelope-caps`,
`J-minimal-anchor-closure`, `J-escape-episode-dichotomy`,
`J-empty-odd-pe-forward`, `J-pe-preimage-intersection`,
`J-pe-walk-predictors`, `J-odd-run-itinerary-grammar`,
`J-block-map-q-state`, `J-cube-even-is-progress`,
`J-cube-odd-even-below-square`, `J-source-relative-odd-reset`,
`J-episode-source-descent`, `J-two-episode-source-descent`,
`J-mixed-oe-defect-gap`, `J-leftover-first-eighth`,
`J-q-return-section-descent`, `J-shared-parity-balance-gap`.

---

## Finance leftover-killers are identities, not movers

Killed claim: a refinement of finance — exact closure, modular
shadows, ordered excursion, prefix feasibility/weight, realizable
tax, remainder, defect correlation, loss persistence, run extremum,
Fourier spectrum, valley coupling, entry corridor/excursion, cyclic
valley, equal valleys, second valley, ceiling finance, \(L=84\) at
floor \(261\), peak count, cluster Amplify, descent next-run,
trajectory budget, cell bridge, almost-search, exponent budget,
block transfer/potential, peak–valley composition, defect congruence
— empties a surviving \((L,o)\) or kills leftover \(84\) at \(m\ge 3\).
Kill: `image_eq_start_defectRatio`, `cycleMin_finance`, unique odd
parent, or a witness below the claimed threshold. One vanishing crumb
does not move leftovers. Residual-floor raise to \(1981\)/\(4756\) is
**PARK**, not a kill; `juggler_cycle_finance_l84_floor_4756` is
`REFUTED` as “the cheapest kill”.
Kind: `REFUTED` / `REPARAMETERIZATION`.
Do not reopen: leftover-killer packaging of cells or finance.

Members: `juggler_cycle_closure_leftover_killer`,
`juggler_cycle_conditioned_closure_leftover_killer`,
`juggler_cycle_mod_closure_leftover_killer`,
`juggler_cycle_ordered_excursion_leftover_killer`,
`juggler_cycle_prefix_feasibility_leftover_killer`,
`juggler_cycle_prefix_weight_leftover_killer`,
`juggler_cycle_realizable_finance`,
`juggler_cycle_remainder_finance_leftover_killer`,
`juggler_cycle_defect_correlation_leftover_killer`,
`juggler_cycle_loss_persistence_leftover_killer`,
`juggler_cycle_run_extremum_leftover_killer`,
`juggler_cycle_fourier_leftover_killer`,
`juggler_cycle_valley_coupling_leftover_killer`,
`juggler_cycle_entry_corridor`, `juggler_cycle_entry_excursion`,
`juggler_cycle_cyclic_valley`, `juggler_equal_valleys_leftover_killer`,
`juggler_cycle_all_valleys_equal`,
`juggler_second_valley_leftover_killer`,
`juggler_ceiling_finance_leftover_killer`,
`juggler_l84_m_ge_three_floor_261`, `juggler_cycle_peak_count`,
`juggler_cycle_cluster_amplify`, `juggler_cycle_descent_next_run`,
`juggler_cycle_trajectory_budget`,
`juggler_cycle_finance_cell_bridge`, `juggler_cycle_almost_search`,
`juggler_cycle_exponent_budget`, `juggler_cycle_block_transfer`,
`juggler_cycle_block_potential`,
`juggler_cycle_peak_valley_composition`,
`juggler_cycle_defect_congruence`,
`juggler_cycle_defect_anticluster`,
`juggler_cycle_extremizer_discrepancy`,
`juggler_cycle_finance_l84_floor_4756`.

Dossiers:
[juggler_cycle_closure](problems/juggler_cycle_closure.md),
[juggler_cycle_conditioned_closure](problems/juggler_cycle_conditioned_closure.md),
[juggler_cycle_mod_closure](problems/juggler_cycle_mod_closure.md),
[juggler_cycle_ordered_excursion](problems/juggler_cycle_ordered_excursion.md),
[juggler_cycle_prefix_feasibility](problems/juggler_cycle_prefix_feasibility.md),
[juggler_cycle_realizable_finance](problems/juggler_cycle_realizable_finance.md),
[juggler_cycle_remainder_finance](problems/juggler_cycle_remainder_finance.md),
[juggler_cycle_defect_correlation](problems/juggler_cycle_defect_correlation.md),
[juggler_cycle_loss_persistence](problems/juggler_cycle_loss_persistence.md),
[juggler_cycle_fourier](problems/juggler_cycle_fourier.md),
[juggler_cycle_valley_coupling](problems/juggler_cycle_valley_coupling.md),
[juggler_cycle_entry_corridor](problems/juggler_cycle_entry_corridor.md),
[juggler_cycle_entry_excursion](problems/juggler_cycle_entry_excursion.md),
[juggler_cycle_cyclic_valley](problems/juggler_cycle_cyclic_valley.md),
[juggler_cycle_equal_valleys](problems/juggler_cycle_equal_valleys.md),
[juggler_cycle_second_valley](problems/juggler_cycle_second_valley.md),
[juggler_cycle_ceiling_finance](problems/juggler_cycle_ceiling_finance.md),
[juggler_cycle_l84_m3](problems/juggler_cycle_l84_m3.md),
[juggler_cycle_peak_count](problems/juggler_cycle_peak_count.md),
[juggler_cycle_cluster_amplify](problems/juggler_cycle_cluster_amplify.md),
[juggler_cycle_descent_next_run](problems/juggler_cycle_descent_next_run.md),
[juggler_cycle_trajectory_budget](problems/juggler_cycle_trajectory_budget.md),
[juggler_cycle_finance_cell_bridge](problems/juggler_cycle_finance_cell_bridge.md),
[juggler_cycle_almost_search](problems/juggler_cycle_almost_search.md),
[juggler_cycle_exponent_budget](problems/juggler_cycle_exponent_budget.md),
[juggler_cycle_block_transfer](problems/juggler_cycle_block_transfer.md),
[juggler_cycle_block_potential](problems/juggler_cycle_block_potential.md),
[juggler_cycle_peak_valley_composition](problems/juggler_cycle_peak_valley_composition.md),
[juggler_cycle_defect_congruence](problems/juggler_cycle_defect_congruence.md),
[juggler_cycle_defect_anticluster](problems/juggler_cycle_defect_anticluster.md),
[juggler_cycle_extremizer_discrepancy](problems/juggler_cycle_extremizer_discrepancy.md),
[juggler_amplify_surplus](problems/juggler_amplify_surplus.md),
[juggler_e4_tight_pullback](problems/juggler_e4_tight_pullback.md),
[juggler_length11_nonpullback](problems/juggler_length11_nonpullback.md),
[juggler_cyclemin_necklace](problems/juggler_cyclemin_necklace.md),
[juggler_first_e_e4](problems/juggler_first_e_e4.md),
[juggler_length8_bootstrap](problems/juggler_length8_bootstrap.md),
[juggler_cycle_ooo_scale](problems/juggler_cycle_ooo_scale.md),
[juggler_cycle_word_functional](problems/juggler_cycle_word_functional.md).

---

## Diophantine walls

Killed claim: Baker / Rhin / Simons–de Weger on \(\lvert 3^o-2^L\rvert\)
kills near-convergents at a realistic floor; Paper B analytics merge
into Paper A finance; an \(n\)-dependent lower bound along \(F_1,F_2,F_3\)
escapes Baker dominance; inhomogeneous Wu–Wang supplies a third
coefficient; archimedean closeness couples to a large \(2\)-adic or
\(3\)-adic valuation; a cycle forces two incompatible fan approximations;
\(478245\to 780239\) is a CF-forced class; leftover words are a
one-parameter Christoffel necklace; near-tightness forces a monochrome
tower.
Kill: Rhin/SdW Lemma 12 is weaker than the exact finance gap on every
tested length; merge needs improvement \(32.5\) at \(L=25781\) and
\(223\) at \(L=50508\) against an uncertified constant \(9/8\); \(G\)
is a function of \((L,o_{\min})\) alone; \(\lvert p+\Lambda\rvert\ge 1-\lvert\Lambda\rvert\);
\(3^o-2^L\) is a \(2\)-unit and a \(3\)-unit so Chim 2025 does not
apply at \(p=2,3\); one global \((L,o)\); leftover \(\varepsilon\)
misses classical CF bounds by \(36\times\) at \(478245\); Hamming to
monochrome grows; \(1+q=n^{3^o-2^L}\).
Kind: `REFUTED` / `METHOD_OBSTRUCTION`.
Do not reopen: Baker transfer; Paper A × Paper B merge; affine
\(n\)-gap; inhomogeneous WW; p-adic coupling; fan multipoint;
a laboratory kill of the near-convergents past \(780239\).

Members: `juggler_baker_kills_near_convergents`,
`juggler_cycle_paper_merge`, `juggler_affine_n_gap_escapes_dominance`,
`J-affine-n-gap-escapes-dominance`,
`juggler_inhomogeneous_ww_beats_finance`,
`juggler_cycle_padic_coupling`, `juggler_fan_multipoint_constraints`,
`juggler_fan_successor_rigidity`, `juggler_christoffel_one_parameter`,
`J-christoffel-one-parameter`, `juggler_cycle_near_tight_monochrome`,
`J-cycle-near-tight-monochrome`.

**Complement, not a kill (CLOSE).** The floor-free gap transfer
\(n\log n\cdot\min(\Lambda,1)\le 2L\) (Paper A Thm 4.10, Lean
`cycleMin_gap_transfer`) with Rhin's measure excludes every cycle
with \(L^{14.3}\le n\log n/915\) — the *short* regime, where the
REFUTED floor-level transfer never competed. It reparameterizes the
no-cycle problem as "no long cycle" and excludes nothing the table
did not; the mechanical fixed-point band of a survivor word has the
finance-predicted count and a fair-coin realized parity depth
(\(L=19,84,1054\)). Do not reopen as a short-interval Paper B, a
two-copy Sturmian rigidity, or a longer band scan
([juggler_cycle_mechanical_window](problems/juggler_cycle_mechanical_window.md)).

**Laboratory kill past \(780239\) (CLOSE).** After Baker and
\(N_0\) are forbidden, excluding the fan member \(780239\) at the
frozen floor is not a Juggler construction: gap lower bounds lose
to dominance, the hug DP is \(C_L\), and the next floor
\(5.54\cdot 10^8\) is PARK. The leftover splits into the
already-named CF-quotient question (`juggler_walk_fan_minimum_law`)
and the recorded long-cycle leftover of Paper A §6. Paper D
working draft (family leftover, not a review object):
[juggler_near_convergent_diophantine_note.md](theory/juggler_near_convergent_diophantine_note.md).
Do not reopen as a kill campaign.

Dossiers: [juggler_cycle_gap_baker](problems/juggler_cycle_gap_baker.md),
[juggler_cycle_affine_n_gap](problems/juggler_cycle_affine_n_gap.md),
[juggler_cycle_inhomogeneous_log](problems/juggler_cycle_inhomogeneous_log.md),
[juggler_cycle_padic_coupling](problems/juggler_cycle_padic_coupling.md),
[juggler_cycle_fan_multipoint](problems/juggler_cycle_fan_multipoint.md),
[juggler_cycle_walk_fan_successor](problems/juggler_cycle_walk_fan_successor.md),
[juggler_cycle_christoffel](problems/juggler_cycle_christoffel.md),
[juggler_cycle_near_tight](problems/juggler_cycle_near_tight.md),
[juggler_cycle_diophantine_survivors](problems/juggler_cycle_diophantine_survivors.md).

---

## Walk charge and Denjoy–Koksma

Killed claim: ceiling Christoffel prefix-minimizes the walk; leftover
hug sits within \(1/L\) of \(C_*\); equal-bin occupancy stays within
\(1\); a human arch \(e=O(\max a)\) kills \(478245\) at the certified
floor; a bounded phase correction makes the walk cocycle nonnegative;
\(C_{\mathrm{hug}}\le C_*\).
Kill: greedy `OOEO` undercuts `OOOE`; worst \((C-C_*)L=1.868\) at
\(L=180467\); first bin at \(L=180467\) overshoots by \(3.13\); hug is
the unique maximizer and the certified DP already computes \(C_L\);
at \(L=478245\) / floor \(162849448\) the DP margin is \(0.4334<1\);
kill would need excess \(\kappa\le -11848\) against \(O(55)\); even
square tower \(k^{2^N}\to\cdots\to k\) kills every bounded \(\psi\);
leftover \(C\) exceeds \(C_*\) by up to \(1.57\cdot 10^{-5}\).
Kind: `REFUTED`.
Do not reopen: DK-arch free-kill; Koksma constant \(1\); walk coboundary
as a termination Lyapunov; Christoffel as the unique adversary.

Members: `juggler_walk_christoffel_prefix`,
`juggler_walk_koksma_one_over_L`, `J-cyclemin-walk-koksma-one-over-L`,
`juggler_walk_hitting_one`, `J-cyclemin-walk-hitting-one`,
`juggler_walk_arch_kills_blocker`,
`J-cyclemin-walk-arch-kills-blocker`,
`juggler_walk_phase_correction`.

Dossiers: [juggler_cycle_walk_mechanical](problems/juggler_cycle_walk_mechanical.md),
[juggler_cycle_walk_koksma](problems/juggler_cycle_walk_koksma.md),
[juggler_cycle_walk_envelope](problems/juggler_cycle_walk_envelope.md),
[juggler_cycle_walk_arch](problems/juggler_cycle_walk_arch.md),
[juggler_walk_coboundary](problems/juggler_walk_coboundary.md),
[juggler_cycle_walk_exchange](problems/juggler_cycle_walk_exchange.md).

---

## Paper B, \(K_3\), and harvest counting

Killed claim: a scale-invariant copy of Theorem R bounds \(K_3\);
increment-first linearization; X1-absorption into a freezing integer;
a nested floor without a \(W\)-family; Selberg pair-count /
dispersion completes the route; Theorem-T passenger slot holds the
length-7 remainder; X3 plus Q/R3 freezes \(\kappa_w\); the
integer-\(w\) block at \(\xi\asymp n^{45/32}\) is an engine line; PET
keeps the floor-correction as a coordinate; the horizontal half is
already Theorem R; an outside-toolkit Juggler reading of
\(\sum e(uw^{3/2})\) remains.
Kill: no \(v\)-level \(b\)-runs, forced inner linearization produces a
\(W\)-family at \(\alpha=45/16>9/4\); increment-first and X1-absorption
named dead; every algebraic re-form transfers the \(P^{27/16}\)
amplitude; \(k=1\) harmonic carries weight one; \(\theta_p\) is an
\(n^{27/16}\)-chirp; Lemma X3 freezes \(J\) not \(\kappa_w\);
\(\xi>n\) independently of \(e(uw^{3/2})\); PET first difference
re-enters GG; leftover \(\alpha\in\{-3/8,3/4,15/8\}\) sit below
\(9/4\); every laboratory reading is a killed route, a nearby
reformulation, an isolated monomial already in Lemma X5, or not a
Juggler construction.
Kind: `REFUTED` / `METHOD_OBSTRUCTION`.
Do not reopen: composition door; \(\beta\)-fallback as a weaker
species; PET; Theorem R at \(\lambda=0\); wrap a nested-floor bound as
a Juggler branch. The remaining external question is
[theory/exponent_pair_two_monomial.md](theory/exponent_pair_two_monomial.md).

Rated-line wall BB/GG/JJ is `PARK_STOP` of quantitative \(K_3\), not a
refutation of Conjectures V/HH.

**Tao-type reduction: reformulations that are not weaker.** The
weakest hypothesis on the concentration route is the live pressure /
no-momentum form (`J-tao-pressure-form`, Tao note §10). The
almost-all-cylinder and pair-correlation forms are Walsh
reparameterizations of \(\mathrm H(C,A)\)
(`J-tao-cylinder-forms-reparameterization`); the free term
\(\psi_F\) of the exact map is the infinite-depth live mass of the
\(OO\) cylinder and not a second wall
(`J-tao-free-term-is-live-mass`, note §11). Kind:
`REPARAMETERIZATION`. Do not: re-derive an "almost all cylinders" or
"pair correlation" hypothesis as new; treat \(K_3\) as necessary or
sufficient for the reduction (any \(o(\log\log y)\) initial depths are
free; a word measure fair to depth \(k\) and all-\(O\) afterwards
satisfies every depth-\(\le k\) statement and violates the bound); use
the exact map (6.1) to replace contagion (its upper recursion has the
same critical exponent \(0.507\) and never gives \(\varphi_F\equiv0\));
or feed a Weyl-differencing saving into the Tao depth (per-depth loss
must be below \(2^{1/C}=1.037\); differencing loses \(\ge 2\));
attempt a last-even reset of \(s_\theta\) as a Paper B estimate
(high-walk forward images ending in \(E\) are sparse, so the split
is \(\mathrm H_q\) at unbounded depth);
treat the forward \(S\)-sampling identity for \(Z_d\) as a new wall
(\(S\)-fairness of the live set);
or expand the walk-live Walsh product as a new exponential-sum
campaign (fixed-order characters are \(e^{o(d)}\); the tail is
\(e^{\Theta(d)}\) and two-sided control is the pair-correlation
reparameterization). Direct-attack dossier:
[juggler_pressure_direct](problems/juggler_pressure_direct.md)
(`J-pressure-direct-routes`).

**Kernel localization to \(OOOEE\) / \(OOEOE\) even-block fibers.**
Killed claim: Paper B Theorem 5.3 localizes to those fibers (fate
note §7.4: leftovers \(\le P^{7/16}\) against \(YP^{-1/24}=P^{0.677}\)
at the \(OOEEE\) length \(Y=P^{23/32}\); forty estimates pending).
Kill: the fibers have length \(Y\asymp P^{5/32}\), target
\(P^{11/96}\); Lemma 3.9's trivial bound is \(\min(Y,P^{89/96})=Y\)
at both candidate lengths, so \(T_2\) has no saving; \(P^{7/16}\)
exceeds the fiber target; \(V\)-retune constraints are disjoint.
Kind: `REFUTED` / `METHOD_OBSTRUCTION`.
Do not reopen: forty-estimate re-derivation; short-interval kernel;
\(V\)-retune; bulk count over a long union of \(m'\) (sparse \(A\)
still needs per-seed mass). The dyadic theorem
`J-kernel-cancellation` is not retagged. Dossier:
[juggler_kernel_localize](problems/juggler_kernel_localize.md)
(`J-kernel-localize`).

Members: `J-scale-invariant-R-extension`, `J-increment-first-K3`,
`J-x1-absorption-K3`, `J-nested-floor-without-W-family`,
`J-dispersion-count-route`, `J-length7-passenger-theorem-t`,
`J-length7-x3-qr3-carry`, `J-length7-integer-w-block`,
`J-harvest-counting-terminal`, `J-horizontal-theorem-r-shortcut`,
`juggler_nil_pet_stays_coordinate`.

Dossiers: [juggler_length7_passenger](problems/juggler_length7_passenger.md),
[juggler_length7_x3_carry](problems/juggler_length7_x3_carry.md),
[juggler_length7_integer_w](problems/juggler_length7_integer_w.md),
[juggler_harvest_counting](problems/juggler_harvest_counting.md),
[juggler_lambda0_nil_transfer](problems/juggler_lambda0_nil_transfer.md),
[juggler_nil_pet_reentry](problems/juggler_nil_pet_reentry.md),
[juggler_horizontal_weyl](problems/juggler_horizontal_weyl.md),
[juggler_nil_horizontal_weyl](problems/juggler_nil_horizontal_weyl.md),
[juggler_v94_hardy_lift](problems/juggler_v94_hardy_lift.md),
[juggler_v94_rate_free](problems/juggler_v94_rate_free.md),
[juggler_rate_free_floor_hardy](problems/juggler_rate_free_floor_hardy.md),
[juggler_ps_inversion_barrier](problems/juggler_ps_inversion_barrier.md),
[juggler_bi_resonance_limit](problems/juggler_bi_resonance_limit.md),
[juggler_parity_discrepancy_transfer](problems/juggler_parity_discrepancy_transfer.md).

---

## Flights

Killed claim: composed record widths multiply constraints; odd towers
are an itinerary-exclusion law; DK prices a kill without \(x_L=n\);
valley composition excludes descent-free flights; interval ET iterates
to depth \(2\); a realizable \((19,12)\) landing forces an extra O or
another \(R_\varepsilon\); reverse fan-admissibility is new; shrinking
odd-inverse width is a new obstruction.
Kill: lattice is an additive monoid; every lab route into
\(\mathcal T_\infty\) is recorded negative knowledge; DK prices hug
prefixes without closure; occupancy is the existing pigeonhole;
\(V(I)\) is \(3\lfloor\sqrt x\rfloor\)-separated (ratio \(\to 9/2\));
twelve-plus-five hug-follow-die holdouts; one-\(W\) inverse occupancy
is `follows`; width \(<1\) is MVT.
Kind: `REFUTED` / `REPARAMETERIZATION`.
Do not reopen: flight composition, odd-tower placement, DK-as-kill,
valley-composition exclusion, interval-ET depth \(2\). Exclusion of
divergent orbits is not claimed.

Members: `juggler_fan_landing_two_way`.

Dossiers: [juggler_flight_record_composition](problems/juggler_flight_record_composition.md),
[juggler_odd_tower_fragment](problems/juggler_odd_tower_fragment.md),
[juggler_flight_dk_pricing](problems/juggler_flight_dk_pricing.md),
[juggler_flight_valley_composition](problems/juggler_flight_valley_composition.md),
[juggler_hug_flow_depth_two](problems/juggler_hug_flow_depth_two.md),
[juggler_flight_fan_landing](problems/juggler_flight_fan_landing.md),
[juggler_hug_prefix_realization](problems/juggler_hug_prefix_realization.md).

---

## Other applications (engine and literature gates)

Killed claim: a laboratory engine campaign or literature gate produces
a new theorem beyond the classical statement.
Kill: surviving statements are `KNOWN` or `REPARAMETERIZATION`
(Černý residual-quotient, \(k\)-abelian finite residual, 3-adic
dictionary, local-vs-global root counts, Erdős signed-kernel
definition, digital-root / weight-dynamics controls, Skolem
leftovers, home-prime 49 prefix, Matthews mod-3 branches, cyclic tag,
reverse-and-add closure, \(7x+1\) class, switching affine,
companion-shift order 6).
Kind: `KNOWN` / `REPARAMETERIZATION`.
Do not reopen: these as Juggler or BT-core frontiers.

Dossiers: [cerny_bt](problems/cerny_bt.md),
[kabelian_complexity](problems/kabelian_complexity.md),
[erdos_distinct_subset_sums](problems/erdos_distinct_subset_sums.md),
[balanced_ternary_digit_sum_dynamics](problems/balanced_ternary_digit_sum_dynamics.md),
[balanced_ternary_weight_dynamics](problems/balanced_ternary_weight_dynamics.md),
[balanced_ternary_weight_drift](problems/balanced_ternary_weight_drift.md),
[balanced_digit_sum_polynomials](problems/balanced_digit_sum_polynomials.md),
[skolem_lrs](problems/skolem_lrs.md),
[skolem_order2_known_zero](problems/skolem_order2_known_zero.md),
[skolem_order5_unconditional](problems/skolem_order5_unconditional.md),
[home_prime_49](problems/home_prime_49.md),
[matthews_prize_mod3_avoider](problems/matthews_prize_mod3_avoider.md),
[cyclic_tag_bit](problems/cyclic_tag_bit.md),
[reverse_and_add_base3](problems/reverse_and_add_base3.md),
[mx_plus_r_7x1_class_obstruction](problems/mx_plus_r_7x1_class_obstruction.md),
[switching_affine_z2_origin](problems/switching_affine_z2_origin.md),
[companion_shift_order6_zero_class](problems/companion_shift_order6_zero_class.md),
[misere_quotients](problems/misere_quotients.md).

---

## Parked, not killed

These are `PARK_STOP`: interesting or blocked, not refuted. Do not
continue automatically. Parked modules stay in the tree and are not a
second frontier.

- **Rated \(K_3\)** behind BB/GG/JJ. Conjectures V/HH stay open.
- **Further descent floors.** The \(3.48\cdot 10^8\) campaign is
  executed (\(N_0=350000000\), period \(\ge 780239\)). Next useful
  floor is \(5.54\cdot 10^8\) (DK break-even of \(780239\)); the
  next *seed* \(16785921\) waits at \(4.54\cdot 10^{11}\). Do not
  open \(N_0=5.54\cdot 10^8\).
- **Residual floor \(1981\)/\(4756\)** for leftover \(84\)
  ([juggler_cycle_l84_residual_floor](problems/juggler_cycle_l84_residual_floor.md)).
- **Hug-cylinder construction** depth \(\ge 2\); depth \(1\) is
  `J-hug-flow-window-depth-one`
  ([juggler_hug_cylinder_construction](problems/juggler_hug_cylinder_construction.md)).
- **Fan concat** / post-19 tails: no \(19\to 19\) on existing windows.
- **Word Atlas**, certificate harvest, probabilistic, extremal control,
  odd-image discrepancy, four-even short-gap \(Z_4\), decoration budget,
  walk sharpness (excess arch as observation).
- **Engine PARK:** Syracuse, BB5, aliquot, vector affine, residual
  complexity, primes enumerator, lifting dossier-as-a-whole, linear
  constraint loops, positivity LRS, piecewise-affine census, matrix-word
  invariant, control obstruction / word composition, engine campaign,
  additive combinatorics, sparse polynomials, perfect powers, lychrel.

Do not treat PARK enumerators as mathematical failures.

---

## Source inventory

Every `conjectures/refuted` id, every ledger `REFUTED` id, and every
dossier whose Decision section contains `CLOSE` appears below or in a
cluster above. MIXED Decision sections (PROMOTE that name a child
CLOSE) are included so the completeness gate cannot hide them.

### Additional ledger REFUTED

`J-ceiling-finance-leftover-killer`, `J-equal-valleys-leftover-killer`,
`J-kernel-localize`, `J-l84-m-ge-three-floor-261`,
`J-second-valley-leftover-killer`.

### Additional CLOSE / MIXED dossiers

[juggler_2adic_integer_bridge](problems/juggler_2adic_integer_bridge.md),
[juggler_above_anchor_first_fail](problems/juggler_above_anchor_first_fail.md),
[juggler_corridor](problems/juggler_corridor.md),
[juggler_cube_crossing](problems/juggler_cube_crossing.md),
[juggler_cumulative_floor_loss](problems/juggler_cumulative_floor_loss.md),
[juggler_cycle_budget_opt](problems/juggler_cycle_budget_opt.md),
[juggler_cycle_diophantine](problems/juggler_cycle_diophantine.md),
[juggler_cycle_diophantine_survivors](problems/juggler_cycle_diophantine_survivors.md),
[juggler_cycle_extremal_composition](problems/juggler_cycle_extremal_composition.md),
[juggler_cycle_lean_consolidate](problems/juggler_cycle_lean_consolidate.md),
[juggler_cycle_walk_fan_growth](problems/juggler_cycle_walk_fan_growth.md),
[juggler_cycle_walk_sharpness](problems/juggler_cycle_walk_sharpness.md),
[juggler_cyclic_feasibility](problems/juggler_cyclic_feasibility.md),
[juggler_drift_crossing](problems/juggler_drift_crossing.md),
[juggler_drift_first_passage](problems/juggler_drift_first_passage.md),
[juggler_escape_state](problems/juggler_escape_state.md),
[juggler_expanding_grammar](problems/juggler_expanding_grammar.md),
[juggler_expanding_residual_concat](problems/juggler_expanding_residual_concat.md),
[juggler_expansion_slack](problems/juggler_expansion_slack.md),
[juggler_finite_dynamics_paper](problems/juggler_finite_dynamics_paper.md),
[juggler_flight_envelope](problems/juggler_flight_envelope.md),
[juggler_flight_fan_concat](problems/juggler_flight_fan_concat.md),
[juggler_flight_post19_tail](problems/juggler_flight_post19_tail.md),
[juggler_floor_boundary](problems/juggler_floor_boundary.md),
[juggler_four_even_short_gap](problems/juggler_four_even_short_gap.md),
[juggler_growth_balance](problems/juggler_growth_balance.md),
[juggler_isolated_odd_return](problems/juggler_isolated_odd_return.md),
[juggler_kernel_localize](problems/juggler_kernel_localize.md),
[juggler_landing_parity](problems/juggler_landing_parity.md),
[juggler_landing_valuation](problems/juggler_landing_valuation.md),
[juggler_lean_architecture](problems/juggler_lean_architecture.md),
[juggler_leftover_cell_lag](problems/juggler_leftover_cell_lag.md),
[juggler_macro_event](problems/juggler_macro_event.md),
[juggler_minimal_counterexample](problems/juggler_minimal_counterexample.md),
[juggler_minimal_survival](problems/juggler_minimal_survival.md),
[juggler_nc_boundary](problems/juggler_nc_boundary.md),
[juggler_odd_chain_minimality](problems/juggler_odd_chain_minimality.md),
[juggler_odd_escape_corridor](problems/juggler_odd_escape_corridor.md),
[juggler_odd_even_reset](problems/juggler_odd_even_reset.md),
[juggler_odd_landing_sets](problems/juggler_odd_landing_sets.md),
[juggler_odd_odd_residual](problems/juggler_odd_odd_residual.md),
[juggler_odd_source_return](problems/juggler_odd_source_return.md),
[juggler_parity_balance](problems/juggler_parity_balance.md),
[juggler_prefix_bunched](problems/juggler_prefix_bunched.md),
[juggler_prefix_nc_admissibility](problems/juggler_prefix_nc_admissibility.md),
[juggler_probabilistic_ld](problems/juggler_probabilistic_ld.md),
[juggler_sequence](problems/juggler_sequence.md),
[juggler_sequential_mordell](problems/juggler_sequential_mordell.md),
[juggler_source_relative_odd](problems/juggler_source_relative_odd.md),
[juggler_stopping_prefix](problems/juggler_stopping_prefix.md),
[juggler_twin_flight](problems/juggler_twin_flight.md),
[juggler_two_step_parity](problems/juggler_two_step_parity.md),
[research_engine_v24](problems/research_engine_v24.md).

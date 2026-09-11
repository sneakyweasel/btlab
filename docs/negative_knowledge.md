# Negative knowledge

## Paper B: the offset composite must subtract the frozen integer floor

The historical Theorem 5.3 Step 5(a) prints 729/512 as the leading
coefficient of the nonzero-offset anchor plus its center mode.
The full phase is c(G-J)-NX, where J=floor(G), with J and N frozen
on each interval. Its leading curvature coefficient is

945/512 - 81/512 - 216/512 = 81/64.

The missing 81/512 is c''J: J=G+O(1), so it cannot be dropped
from the leading curvature. Kind: **REFUTED** displayed identity.
The old positive numerical margins must not be carried over
without this subtraction. This does not refute a power saving.

The [corrected offset proof](theory/paper_b_offset_anchor_report.md)
centers the coefficient and truncates residual modes below the
curvature-cancellation range, giving O_epsilon(P^(23/24+epsilon))
for its stated family. The subsequent
[dyadic assembly](theory/paper_b_kernel_assembly_report.md) proves
the weaker undecorated monomial kernel with exponent 127/128.
The subsequent
[OOOEE transfer](theory/paper_b_oooee_transfer_report.md) proves the
specific four-coordinate modes with exponent 127/128 and the
five-step certificate density 7/8 as AI-assisted written results,
pending independent review. The 95/96 target, arbitrary decorations,
and short-interval localization remain unproved.
Source: [branch dossier](problems/juggler_paper_b_offset_anchor.md).
Ledger: J-paper-b-offset-composite-729.
Exact regression control: tools/validate_paper_b_offset_anchor.py.

## Paper B: individual wave size does not imply combined dominance

The historical Paper B Theorem 5.3 Step 5(b) classifies two signed
differenced waves by the maximum of their individual scales.
For h_1=h_2=1 and u'=-u, their sum is identically zero, while that
maximum can exceed the zero-offset anchor scale by a growing factor.
For h_2=2h_1 and u'=-u/2, the combined wave is
-(u/2) Delta_(2h_1)^2 Y. An individual-mode estimate therefore cannot
be substituted for an estimate of the complete signed phase.

Kind: **REFUTED** / method obstruction for this dominance inference.
This does not refute the desired kernel estimate or OOOEE density.
The subsequent
[signed zero-offset proof](theory/paper_b_signed_waves_report.md) bounds
the combined family by O_epsilon(P^(31/32+epsilon)), including the
specified D2 factors. It uses signed curvature and Fourier weights.
The original dominance inference remains refuted. The subsequent
[dyadic assembly](theory/paper_b_kernel_assembly_report.md) proves
the weaker undecorated monomial bound with exponent 127/128.
The subsequent
[OOOEE transfer](theory/paper_b_oooee_transfer_report.md) proves the
specific four-coordinate modes with exponent 127/128 and the
five-step certificate density 7/8 as AI-assisted written results,
pending independent review. The 95/96 target, arbitrary decorations,
and short-interval localization remain unproved.

Source: [D2 supplement](theory/paper_b_d2_report.md), Section 8;
[branch dossier](problems/juggler_paper_b_d2_repair.md).
Ledger: J-paper-b-signed-wave-dominance.
Do not reuse the maximum-of-individual-scales dominance inference
without controlling cancellation in the combined phase.

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

## Three-paper review corrections (9 September 2026)

- **General exact monomial fibers are false.** The exact orbit
  \(1015\to32336\to179\to2394\to48\to6\) has word \(OEOEE\), but
  \(7^{32}\le1015^9<8^{32}\). A production's exponent product therefore
  does not identify its exact nested-floor fiber. Paper C Model calculation 5.13
  now separates the smooth model from the required exact-fiber argument;
  iterated ceiling endpoints repair the finite \(V_k\) fibers. Their
  fixed-depth boundary error is smaller than the established asymptotic
  counting error, preserving the finite exponent 0.4926; the old explicit
  constants remain smooth-window constants, not exact-fiber certificates.
- **The new kernel application used the wrong scale.** \(OOOEEE\) and
  \(OOEOEE\) have nominal inverse-fiber length \(P^{37/64}\), not
  \(P^{23/32}\). Theorem 5.5's unchanged-saving threshold \(29/48\)
  exceeds \(37/64\). The formal smaller-scale saving \(11/1536\) is a
  proof obligation, not an established production or contagion dividend.
- **Hypotheses cannot be dropped in the reductions.** The biased rate
  is \(q\)-dependent and limited by the accumulated additive-error budget;
  optimizing a tilted hypothesis requires that hypothesis at the optimizer.
  Paper A's charge obstruction also needs an explicit positive anchor lower
  bound, not merely a bound at actual cycle minima. Neither correction
  opens a new termination route.

Sources: [Paper A](theory/juggler_finite_dynamics_note.md),
[Paper B](theory/juggler_parity_discrepancy_note.md),
[Paper C](theory/juggler_fate_almost_all_note.md), and the corrected
[cycle-run dossier](problems/juggler_cycle_run_alphabet.md).

## Agent filter

Three tests, same wording as `.cursor/rules/methodology.mdc`:

- Cycle: stronger lower bound on `|3^o-2^L|` than finance, or a constraint on `(L,o)` other than one global pair
- Termination: a Juggler construction of `e(uw^{3/2})` not in the killed toolkit; nested-floor / two-monomial is exported
- Local: more than parity + interval; otherwise Collision Factorization

`Already killed by?` names the index cluster or which test fails;
`none` only with a reason. Leftover-killer slogans with no new identity
are `REPARAMETERIZATION` (`CLOSE`).

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
[juggler_parity_complexity](problems/juggler_parity_complexity.md),
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

**Frontier parity is not automatic (CLOSE).** The letter after an odd
step, \(\lfloor (2k+1)^{3/2}\rfloor \bmod 2\), has factor complexity
\(p(L)\ge L^2/8-O(L)\): every equal-interval rotation word occurs, by
Taylor expansion and joint equidistribution of \((f,f')\bmod 2\)
(Boshernitzan, no nested floor at depth one), while automatic sequences
have \(p(L)=O(L)\) (Cobham). Do not attempt Walnut, Ostrowski-automatic,
or any finite-state decision procedure on Juggler frontier parity, at
any depth: depth one already fails, and deeper letters are nested floors
outside the Hardy reduction
([juggler_parity_complexity](problems/juggler_parity_complexity.md),
`J-parity-sequence-complexity`).

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

**Read `parity_holds`, not the name (added after a four-entry
misreading of my own).** Corollary 4.5's "length-only parity charge" is
**not** a two-class parity split of odds at \(n\) and evens at
\(n^{2}\). It is the three-class bound
\(\theta\le(6/5)[e/(n\log n)+(o-e)/(t\log t)+e/(2n^{2}\log n)]\), with
the internal odds at \(t=\lfloor n^{3/2}\rfloor\) — that is
`threeTerm_bound`, and it carries no hypothesis about `EE`. So the
cutoff \(25781\), the \(141\) lengths, and the floors of Theorems 5.2
and 5.9 and Corollaries 5.10, 5.11 and 5.14 are all free of the run
packing. **No period bound in Paper A depends on Theorem 4.7**; its only
consumers are Theorem 4.8 and Proposition 4.9's identification with
\(\mathcal E_{\mathrm{run}}\). Before treating a gap in 4.7 as
load-bearing, check what actually cites it.

**The one-line reason (added after the ordered-vector retry).** Every
member of this family compares the accumulated floor defect \(\Delta\)
against the formal surplus \(G=n^{3^{o}}-n^{2^{L}}\). By
`global_defect_identity`, \(\Delta=n^{3^{o}}-T_w(n)^{2^{L}}\), so
subtraction gives

\[
\Delta-G \;=\; n^{2^{L}}-T_w(n)^{2^{L}} .
\]

No local remainder, no transport weight, no seam split and no ordering
survives on the right. So *any* comparison of \(\Delta\) with \(G\) ---
size, sign, congruence, fractional part --- is a restatement of
\(T_w(n)\) against \(n\), and no reweighting or reordering can change
that, because none of it appears. Verified on \(1358\) realized records.
The residues of \(T_w(n)-n\) attain every class mod \(3,5,7,8,9,16\)
inside each of `OOE`, `OOEOOE`, `OEOOOE` within at most \(66\) realized
starts, which is `cycle_mod_closure` from below; the window bound
\(2Y+1>m\) gives it from above at \(n\ge 10^{6}+1\).
The same closes every *part*: the ordered decomposition
\(\Delta=\sum_i W_ie_i+X\) has \(e_i\ge0\) and \(X\ge0\) (6615 records,
no exception), so Amplify, the largest single \(e_i\) and either seam
half are all at most \(\Delta\), hence below \(G\) on every expanding
word. Amplify\(/G\) does climb --- \(0.18,0.32,0.65,0.84,0.95\) on
\(\mathtt{O}^{k}\mathtt{E}\) at \(L=8,\dots,12\) --- but that is the
approach to the contraction boundary, not to a usable threshold.

Do not reopen: reweighting, reordering, or reducing the floor-defect
comparison mod anything, nor bounding any single part of it.

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

## Paper A's mechanisms have measured ceilings

Killed claim: a bigger descent floor, a sharper per-length charge, or a
longer shape enumeration reaches "no nontrivial cycle".

**The floor route diverges.** Finance excludes \(L\) when
\(n_{\max}(L)\le N_0\), and along the convergents
\(n_{\max}(q_k)\log n_{\max}\approx 0.45\,q_k q_{k+1}\) — flat to within
a factor \(1.3\) over \(q_k=19\ldots176251\). \(q_{k+1}\) is unbounded,
so \(n_{\max}\) is. Every length needs its own floor. Raising \(N_0\)
buys \(\text{period}\asymp\sqrt{N_0\log N_0}\) (finance) or
\(\asymp\sqrt{N_0}\log N_0\) (walk charge) — square roots, not the
powers \(N_0^{0.59}\)/\(N_0^{0.69}\) a narrow fit suggests. Doubling the
period costs roughly quadrupling the floor, and no exponent helps,
because the target recedes. Any result that
fixes \(L\) and asks for a floor is a period bound, never a cycle
theorem.

**The shape route is exponential, and its law is empty where it
matters.** Section 3's exclusions are the only floor-free *and*
length-free family. Admissible shapes at the least odd count grow about
\(6\times\) per even letter: \(2651\) at \(e=7\) (Theorem 3.31's
frontier), \(1.1\cdot10^{13}\) at \(e=20\), against \(e=9515\) for the
first surviving length. But feasibility is not the real obstruction.
Theorem 3.26's law — the whole word expands, no proper odd-starting tail
does — is, after complementing tail to prefix, the anchor
\(3^{o_p}\ge2^{\lvert p\rvert}\) raised to \(1+\theta\). Its whole
strength over the anchor is the surplus. It kills \(41\%\) of shapes at
\(e=10\) (\(\Lambda\approx0.37\)) and **exactly none** at \(e=31\),
\(210\), \(389\) (\(\Lambda\le2.1\cdot10^{-3}\)) — at \(e=389\) the two
counts agree in all \(300\) digits. Surviving lengths have
\(\Lambda\in [3.6\cdot10^{-6},6.9\cdot10^{-5}]\).

**So finance and the run--suffix law fail for one reason.** Finance weakens as
\(\theta\to0\) because \(n_{\max}\sim1/\theta\); the run--suffix law
weakens as \(\theta\to0\) because it is the anchor tightened by
\(1+\theta\). They cannot be played against each other: the lengths where
one is weak are exactly the lengths where the other is. **Any method
whose strength is measured by the surplus is empty where a cycle could
be.** Do not open a direction whose kill criterion is a function of
\(\theta\).

**What is actually missing.** The only proved relation between minimum
and period runs one way: finance bounds \(n\log n\lesssim L^{\mu}\), and
\(\mu\ge2\) for every irrational, so even a perfect irrationality measure
leaves \(n\lesssim L^{2}\). Nothing bounds \(n\) *below* in terms of
\(L\) — the descent floor is a constant, and counting the \(L\) distinct
states gives no window, since a cycle's states are not confined to one.
Survivors sit at \(n\approx L^{1.7}\), inside the band a one-sided bound
cannot empty. Reopen only on a lower bound for the minimum in terms of
the period, or an argument uniform over shapes.
Kind: `REPARAMETERIZATION` / `PARK_STOP`.
Branch: [juggler_cycle_method_ceilings](problems/juggler_cycle_method_ceilings.md).

## The elementary production ladder is finished

Killed claim: the next truncation \(V_k\) of the elementary production
family is the best next question; more rungs lower the rate the Tao
pressure must beat; the family's \(0.4927\) ceiling is far enough above
\(\lambda^{**}\) to be worth climbing toward.
Kill: the ceiling was always known -- production-note Theorem 5 collapses
the family to \(x+y/3=1\), root \(0.4926580\) -- and nobody priced the
residual. \(\lambda^{**}\) reaches the reduction through one number, the
required rate, and that feeds *discrete* constants. Every one of them
reaches its terminal value at \(V_5\): least \(C=19\), \(C(0.5)=19\),
\(C(0.55)=41\), unchanged at every later rung and at the limit. So the
\(V_6\) audit moved \(\lambda^{**}\) by \(2.1\cdot10^{-4}\) and changed no
constant, and the whole remaining infinite ladder is worth
\(8.6\cdot10^{-5}\). The nearest threshold, Azuma \(q=0.55\) dropping
\(41\to40\), needs \(\lambda>0.510018\): short by \(0.01736\), which is
\(201\) times everything the family has left. Chernoff needs
\(\lambda>0.519593\) and Azuma \(q=0.5\) needs \(\lambda>0.522563\). The
one continuous consumer, `failure_margin`, does move -- by
\(7.5\cdot10^{-6}\), which is \(1.3\cdot10^{-4}\) of the \(0.06\) census
resolution it is read against. Gaps to the limit fall by \(y/3=0.28929\)
per rung, so no reindexing accelerates it either.
Kind: `MEASUREMENT` / `PARK_STOP`.
Branch: [juggler_vk_ladder_ceiling](problems/juggler_vk_ladder_ceiling.md).

Do not open \(V_7\) or any later truncation; do not reopen as a sharper
tail estimate, a faster-converging reindexing, or a combined \(V_k\)
bound. Anything that moves a constant must move \(\lambda\) by at least
\(0.0174\), two hundred times more than the family contains, so it has to
come from outside the family -- the \(r\ge2\) rungs, which need genuinely
nested floors and are exported to Paper B. \(\lambda^{**}=0.4926\) stands.

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

**Cycle height-to-alphabet inference withdrawn (CLOSE; corrected 9 September 2026).**
The Lean odd-run inequality is upper growth \(y^{2^r}\le v^{3^r}\),
not the lower growth needed for \((3/2)^r\le R\). Exact \(9\to27\to140\)
also disproves the factor-free two-step inference: \(140^4<9^9\).
Retain \(m^9<2(M+1)^4\), the even-run bound \(2^g\le R\), and the
conditional word identities only. Actual nontrivial cycles have positive
floor drift, not exact logarithmic closure, so neither a two-block alphabet
from \(R<27/8\), exact block proportions, nor height equal to discrepancy
is established. The prescribed-prefix Lean results do not fix the first
fall after exactly three climbs. The necklace census is an abstract model,
not realized cycle geometry. Do not reopen as a cycle kill, a
certificate-density argument, or a longer necklace census
([juggler_cycle_run_alphabet](problems/juggler_cycle_run_alphabet.md),
`J-cycle-run-alphabet`, `J-cycle-band-discrepancy`).

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
weakest per-scale hypothesis in the displayed hierarchy is the live pressure /
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
For “external averaging” after that CLOSE, completing the single live-tilted odd sum
without a Walsh expansion of the tilt is a cylinder-weighted nested
phase (Vaaler of \(1_{\mathrm{odd}}(J^t n)\); Walsh tail, two-monomial
/ Weyl \(cC<1\), or §10.4(e)); the harmonic average of live counts is the
finite-depth log-measure live mass (`J-tao-free-term-is-live-mass`);
the odd step of a production recursion is tilted \(S\)-fairness.
Parseval / large sieve is the pair-correlation form already named
above. Do not reopen as a signed Walsh tail, a short-interval Paper B
on the completed sum, or a third formulation. Dossier:
[juggler_pressure_external_average](problems/juggler_pressure_external_average.md)
(`J-pressure-external-average`).
**Correction, 9 September 2026:** the rejection of the already-defined
Cesàro pressure average is withdrawn. A growing harmonic upper bound
can beat the faster-growing contagion lower bound. Precisely, with
\(\rho_k=Z_{d_k}(2^k)/(N_k a^{d_k})\), cumulative bound
\(\sum_{k\le K}\rho_k\le K^{1+\eta+o(1)}\) is sufficient when
\(r-\eta>1-\lambda^{**}\), where
\(r=C(\theta p_C-\log a)/\log2\). Markov per block followed by
summation gives odd harmonic failure mass
\(O((\log x)^\beta)\) for every
\(\beta>\max\{1+\eta-r,0\}\); even fibers preserve that bound
for \(\beta>0\). `J-pressure-scale-average-suffices`, EXACT — HUMAN
PROOF. The original \(\Pi\) has \(\eta=0\), so it suffices at
\(C=19\). This corrects sufficiency only; neither \(\Pi\) nor a
Juggler-specific method to estimate it is proved. A small arithmetic
mean of the tilted excess is not its exponential moment.

**Scale-average estimate follow-up (PARK, 9 September 2026).** The
corrected conditional implication is retained. The actual sparse
source set consisting of odd square starts or odd starts with square
successor has only \(O(y^{3/4})\) members per block, hence bounded
total normalized pressure over all scales
(`J-pressure-sparse-starts`). This does not control the complement or
relative live shares. Merely counting exceptional scales while using
the trivial cap on them is insufficient: at \(C=19\) the cap is
\(\rho_k\ll k^{4.8934268}\), whereas the permitted cumulative power
is below \(1.0195266\). Even a superlacunary unbounded exceptional set
allows a scalar capped-spike sequence exceeding that budget. This is
not a realized Juggler counterexample or a refutation of the scale
average. Do not promote sparsity of scales without bounding their
weighted amplitudes. Dossier: the external-average link above.
The next finite-prefix/suffix-cap test is also closed: any fixed
prefix information leaves the cap exponent unchanged. With fair
normalization, \(r-\eta>0.5074\), \(\eta\ge0\), and arbitrary
\(C,\theta\), Jensen's inequality gives
\(\kappa-1-\eta>0.9376802680\). Thus fair tilt/depth tuning cannot
repair that trivial cap. This is not a bound from below for actual
pressure and is not asserted for arbitrary normalizations. The
necessary all-odd density saving at the original \(C=19\) remains
unproved (external-average dossier (C1)–(C3)); no new named hypothesis.
The subsequent one-sided sieve check closes a narrower information-only
route, not the arithmetic count: for every depth d and order h<=d-1,
there are abstract binary distributions with a forced initial odd
letter and exactly fair joint marginals of all orders <=h, yet all-odd
mass at least 1/(2 sum(binom(d-1,j),j=1..h)). A random binary matrix
and a union bound prove this. For h=o(d), the lower bound is exp(-o(d)),
larger than the exp(-c*d) required by (C3). Thus those marginals alone
cannot supply the desired sieve bound. No model is asserted to be a
Juggler distribution; map-specific arithmetic inputs are not excluded.
See the same dossier (D1)–(D3). The parent estimate stays PARK.
The direct-source follow-up adds no escape from these limits. The
neighbor theorem's elementary block cover deletes only a fraction
of order y^(-1/4), not a logarithmic-power fraction after log-log depth;
iteration on selected sources is unproved. Replacing actual defects
n_j³-n_(j+1)² by free residues modulo an even Q admits every odd
state-residue chain when each defect window contains [0,Q-1]; this
does not rule out sieves using the actual defect correlations.
Finally d_k-d_K<=19 on K<=k<=2K at C=19 lets one freeze depth at a
constant pressure cost, but d_K still grows; truncating further to
fixed depth restores (C1). These are scope checks, not new named
theorems or a refutation of (C3). The three shortcuts are CLOSE;
the actual count remains PARK. See the direct-source follow-up in
the external-average dossier above.
The fixed-base, long-square-dilation transfer is also closed
(external-average dossier (E1)–(E3)): sources n=a²b admitting a>=A
number at most 2y/(A-1), while at least 3y/8-sqrt(2y)-1 odd sources
are squarefree and have only a=1. Thus long-parameter balance does
not cover the bulk. Two-letter membership is not dilation-invariant
(3 versus 27, 7 versus 175); at the second iterate the fractional-part
term grows like a^(3/2). This closes only that averaging transfer,
not squarefree counting, every dilation method, or the actual (C3).
Squarefreeness also fails to give a uniform positive fractional-floor
gap: infinitely many c>1, c=1 mod18, have c,2c-1,2c+1 squarefree;
then n=4c²-1 is squarefree, J(n)=8c³-3c is odd and nonsquare, and
0<n^(3/2)-J(n)<1/(5c). The elementary union bound gives at least
X/72-3sqrt(2X+1)-2 such c up to X. This thin two-letter family does
not challenge the growing-depth count. The Möbius squarefree expansion
has tail <=2y/A uniformly in depth but no bound for its retained signed
sum was found. See the same dossier (F1)–(F3); do not label possible
Möbius cancellation or the actual squarefree count refuted.
The subsequent two-step fractional-gap shortcut also fails after
excluding all square states: for odd a>=7, n=a^4-8 has exact odd
images m=a^6-12a² and z=a^9-18a^5+54a. For prime a>=7 all three
are nonsquares, while the two fractional errors are <25/a² and
<225/(2a³), both tending to zero. This says nothing about quartic
squarefreeness. The integer defects grow, and the transported error
n^(9/4)-z is asymptotic to 36a, so arbitrary weighted or growing-depth
error budgets are not refuted. The explicit family has O(y^(1/4))
sources and is covered by the sparse-source bound (B1). The narrow
positive two-step unweighted-gap claim is CLOSE; (C3) stays PARK.
Proof and scope: external-average dossier (F4)–(F6).
Initial boundary trimming does give a source estimate: uniformly in
0<delta<=1/2, the odd starts in (y,2y] with distance of n^(3/2) to the
nearest integer <=delta number O(delta y+y^(5/6)), by Paper B's
second-derivative estimate and Erdős–Turán. At delta=(log y)^(-6),
their restricted normalized pressure is summable at fair optimized
C=19; the exact inequalities 2^30<3^19 and 6^19<2^5 5^19 certify
kappa<5. This controls only the initial strip, not its relative live
share, the complement, or later boundary encounters. Automatic
ambient iteration is CLOSE: after one odd step it yields only
O(delta y^(3/2)+y^(5/4)), vacuous against the original O(y) sources.
This is the known sparse-image obstruction, not a refutation of a
direct late-hit source estimate. Growing-depth trimming and (C3)
remain PARK. Proof and scope: external-average dossier (G1)–(G2).
The prefix-selected follow-up does not overcome depth uniformity.
Paper B's existing S_(0,2h) estimate does control the second strip
directly on sources, with error O_epsilon(y^(23/24+epsilon)); its
restricted pressure is again summable at delta=(log y)^(-6).
This bypasses ambient completion at that fixed depth only. Earlier
good margins do not supply interval averaging along all-odd prefixes:
for the auxiliary F(x)=floor(x^(3/2)), the exact constancy cells of
every F^t are the first cells [m^(2/3),(m+1)^(2/3)), each shorter than
one, because F is injective on positive integers. Margins shrink or
select these cells; counting their source integers remains unproved.
Do not multiply smooth derivatives through an exact floor after its
first-image coalescence, or insert an additional prefix indicator
into an unweighted exponential-sum estimate. This localization
shortcut is CLOSE; actual growing-depth counts remain PARK.
Proof and scope: external-average dossier (G3)–(G4) and its cell check.
Mass, max-atom, collision energy and ancestry multiplicity of the
tilted pushforward \(W_t\) do not force the five-word four-step cut:
they saturate on the injective \(\mathtt{OOOO}\) cell (profile
relabelled, mass \(\times e^{4\theta}\)) or need a location bound on
the support, and landing multiplicity through an \(\mathtt{OE}\)
collision is unbounded. Controlling where the atoms sit is the
good-base / \(\mathrm H_q\) split or the pair-correlation form already
named above. Do not reopen as a concentration statistic, a bounded
ancestral capacity, a location/gap/even-fiber framework, or another
pressure census. Dossier:
[juggler_transfer_weight_invariant](problems/juggler_transfer_weight_invariant.md)
(`J-transfer-weight-invariant`).

**Pointwise logarithmic-weight pressure certificates (9 September 2026).**
The class \(h(n)=(\log n)^{s+o(1)}\), with any real \(s\), cannot
give the uniform killed tilted factor \(a_{\theta,q}=1-q+qe^\theta\)
at an optimizing pressure tilt. Exact live even and odd power towers
force the asymptotic pointwise factor to be at least
\(\max(2^{-s},e^\theta(3/2)^s)\ge e^{\theta\log2/\log3}
>a_{\theta,q}\). The bound is sharp as a limsup and survives every
fixed block length and all subpower arithmetic fluctuations of the
weight. This extends the scope of the old bounded-correction
obstruction; it is not an attempt to rescue that program. The proof
uses pointwise transitions, so it does not refute averaged drift on
the actual dyadic tilted population. Do not turn the necessary
oscillation condition on irregular weights into a new rescue branch.
Dossier: [juggler_pressure_direct](problems/juggler_pressure_direct.md),
`J-pressure-log-order-obstruction`, `J-pressure-log-order-certificate`.
Decision: CLOSE for this certificate class; M and P remain open.

**Unstopped growing-depth cylinders (9 September 2026).** The former
all-word version of \(\mathrm H(C,A)\) is **REFUTED** for
\(C>1,A>1\), and the all-prefix version of \(\mathrm H_q(C,A)\)
for \(q<1,C>1,A>1\): a pure even inverse tree of 4 followed by one
OEE lift produces a single absorbed cylinder of size
\(\ge y/(216\log y)\) on infinitely many dyadic blocks. This is an
exact-map human proof, not the older abstract word-measure example.
The entire prefix cylinder is at 1 and hence sends every member to
an odd next letter. Do not try to prove the full unstopped bounds.
The definitions now restrict H to bad words and H_q to bad prefixes;
the live pressure was already stopped and is unaffected. Dossier:
[juggler_absorbed_cylinder](problems/juggler_absorbed_cylinder.md),
`J-absorbed-cylinder`, `J-unstopped-cylinder-bound`, conjecture
`juggler_unstopped_cylinder_bound`. Decision: CLOSE; no termination
estimate is gained.

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

**First-step locality refinement (9 September 2026).** A universal
opposite-image-parity source-distance bound of o(n^(1/4)) is false,
even on odd nonsquare starts with nonsquare first image. For prime
c >= 37, the consecutive odd offsets t with 1 <= t <= 2 sqrt(c)
give the exact odd images
floor((4c²+t)^(3/2)) = 8c³+3ct, all nonsquare. Central starts need
distance at least n^(1/4)/4 to find the opposite image parity.
These unbounded blocks, not the earlier single length-52 example,
also provide an explicit counterexample to any translation-uniform
sublinear interval-discrepancy bound with a fixed constant.
Qualitative long blocks were already implied by parity complexity;
the new quantitative companion upper bound is 8 ceil(n^(1/4)).
The entire explicit family has only O(y^(3/4)) sources per dyadic
block. This refutes neither longer-distance assignments nor aggregate
pressure; it supplies no prefix-preserving or bounded-multiplicity
pairing. Proof: [parity neighbor scale](problems/juggler_parity_neighbor_scale.md),
`J-parity-neighbor-scale` (EXACT — HUMAN PROOF).

Its direct prefix-pairing follow-up is CLOSE, by the already-recorded
image-gap obstruction: for odd n >= 65536, the entire window
of radius 8 ceil(F(n)^(1/4)) about F(n) contains no other odd-source
image. A target neighbor supplied by the first-step theorem therefore
has no odd pullback. An unrestricted K-to-one assignment between
continuers and exits in the same finite source window exists exactly
when the continuation share is <=K/(K+1); renaming the count supplies
no arithmetic estimate. The calibration K=5 would control the all-odd
pressure contribution only if available throughout the required depth
range. No such construction was found, and neither larger-distance
matching nor the actual growing-depth count is refuted. See Results 4
of the same dossier; no new named theorem or frontier hypothesis.

---


The 10 September consolidated Paper B theorem does give the inherited
four-letter all-odd count N/16+O_epsilon(N^(127/128+epsilon)): sum its
two formal sign classes (-1,-1,-1,+/-1). Direct reuse for a fifth odd
letter is CLOSE. The new coordinate is W=w^(3/2)=w U, whereas the theorem
controls U=sqrt(w); treating w(n) as a fixed Fourier frequency both
loses source independence and exceeds the stated mode range. Freezing
w leaves at most one source. At n=5^8 all four sources are odd, but
floor(sqrt(5^27)) is odd and floor((5^27)^(3/2)) is even. This refutes
that parity substitution only, not a growing-depth count. The corollary
inherits the current AI-assisted Paper B proof and its review limitations.
See the new-theorem transfer subsection of
[the pressure dossier](problems/juggler_pressure_external_average.md).


A separate 10 September block construction supplies a fixed-depth
positive result without rescuing that pullback: classical second-derivative
and Erdos--Turan estimates give even-image count M/2+O(M y^(-1/6)+y^(1/4))
in every M-point odd-source block inside (y,2y]. Large enough constant
multiples of y^(1/4) therefore admit an explicit two-to-one assignment,
with optimal first-step displacement exponent 1/4. Current Paper B
counts extend the assignment through prefix length three, at the
larger radius O_epsilon(y^(127/128+epsilon)). No growing-depth capacity
bound is obtained. These are distinct block assignments, not the
pointwise neighbor choice or its failed target pullback. Details:
[neighbor-scale Results 5](problems/juggler_parity_neighbor_scale.md).


**Fifth-letter uniform last-floor freezing is CLOSE (10 September 2026).**
Writing W=(Z-{Z})^(3/2)=v^(9/4)-(3/2)v^(3/4){Z}+R gives
R=O(P^(-27/16)), so the remainder is harmless for one available
mode. The correction coefficient is order P^(27/16); freezing
{Z} in cells of width P^(-1/24) leaves phase variation of order
P^(79/48), already for mode one. Uniform cellwise approximation
therefore cannot use the current frequency range. The new outer
phase v^(9/4) is also outside the stated theorem. This closes only
that shortcut, not actual fifth-state balance or other analytic
methods. Three reused finite blocks support all 1,209 two-to-one
assignments at prefix four; no uniform capacity follows. Details:
[neighbor-scale Results 6](problems/juggler_parity_neighbor_scale.md).

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

## Geometric \(\{(3/2)^n\}\) equidistribution

Killed claim: a Juggler layer (Paper B, walk charge / Ostrowski,
Baker/Rhin on cycle gaps, fate/Tao, Collatz base-\(3/2\)
numeration) constrains uniform distribution or density of
\(\{(3/2)^n\}\) in \([0,1]\).
Kill: three different \(3/2\) objects; Paper B is a polynomial-floor
phase, walk charge is linear rotation \(\{k\log_2(3/2)\}\), Baker
on \(\lvert 3^o-2^L\rvert\) is a two-term cycle form (already
**REFUTED** as a cycle killer), and the odd-tower dossier already
refused the Mahler flavor transfer. The problem is classical OPEN
(Vijayaraghavan 1940; oscillation \(\ge 1/3\) by
Flatto–Lagarias–Pollington 1995). A GPU census is not a theorem.
Kind: `KNOWN` / `METHOD_OBSTRUCTION`.
Do not reopen: as a Juggler or Collatz successor; Paper B wrap;
walk-charge wrap; Baker wrap; `research/three_halves/`; a
discrepancy census as a theorem. Lean-ifying Vijayaraghavan or
Flatto–Lagarias–Pollington is a new formal area, not Juggler
progress.

Dossiers: [juggler_three_halves_mod_one](problems/juggler_three_halves_mod_one.md).

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
- **Run-type packing fragility**
  ([juggler_cycle_packing_fragility](problems/juggler_cycle_packing_fragility.md)).
  Theorem 4.7's missing no-`EE` hypothesis is priced: it costs \(18\) of
  Theorem 4.8's \(42\) exclusions and no period bound at all. Reopen only
  on a proof that closure at \(o_{\min}(L)\) caps the `EE` density below
  \(50\) adjacencies at \(L=56347\) — which is the packing claim again.
- **Lachesis log-log clock**
  ([juggler_lachesis_loglog_clock](problems/juggler_lachesis_loglog_clock.md)).
  The walk mod 1 is the rotation orbit by \(\log_2(3/2)\), and the walk
  is the log-log clock to \(2\cdot 10^{-10}\) realised
  (\(1.7\cdot 10^{-4}\) bounded on a cycle), so a Lachesis basin is not
  lacunary and carries density \(\gtrsim 1/n\) on *every* dyadic block —
  the third case of contagion note §5.3. The deep natural-density census
  this suggests is `J-lachesis-census-dominated`: reaching cycle minima
  \(\le M\) costs \(M\) shallow orbits as a floor raise against \(M\)
  orbits at \(10^{100}\) to depth \(\approx 500\) as a census. Do not run
  the census. The amplified blocks are answered (none: the \(OE\)
  detour costs \(1/3\) and lands elsewhere); the upper bound on the
  basin is the free term (`J-lachesis-upper-bound-free-term`); a
  Clotho basin gets the same statement only under slow escape, and slow
  escape is neither forced by the flight laws (all lower bounds) nor
  realised by any flight — the seven high-flyers run \(28\)–\(650\times\)
  above the gate at every decade to \(10^{5000}\)
  (`J-clotho-slow-escape-not-forced`). The rate that would make Clotho
  basins provably lacunary is behind the wall: pigeonhole gives
  \(n^{2^B}\) steps in a walk band, and anything better is a
  single-orbit parity statement at depth \(\ln y\)
  (`J-clotho-hug-excess-rate`). Do not open it as a branch. The
  companion question — how long a flight can stay in the hug band — is
  `J-hug-band-residence-is-prefix-realization`: the band word is forced
  (Lean `band_successor_unique`), so residence is
  [hug prefix realization](problems/juggler_hug_prefix_realization.md),
  already CLOSE at \(2^{-L}\) with fill to depth \(28\). Reality is
  \(\log_2 n\); the pigeonhole \(n^3\) is off by the whole scale.
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
`J-clotho-slow-escape-not-forced`, `J-lachesis-census-dominated`,
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
[juggler_depth_one_main_term](problems/juggler_depth_one_main_term.md),
[juggler_drift_crossing](problems/juggler_drift_crossing.md),
[juggler_drift_first_passage](problems/juggler_drift_first_passage.md),
[juggler_effective_tower_height](problems/juggler_effective_tower_height.md),
[juggler_escape_state](problems/juggler_escape_state.md),
[juggler_expanding_grammar](problems/juggler_expanding_grammar.md),
[juggler_expanding_residual_concat](problems/juggler_expanding_residual_concat.md),
[juggler_expansion_slack](problems/juggler_expansion_slack.md),
[juggler_failure_margin](problems/juggler_failure_margin.md),
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
[juggler_transfer_weight_invariant](problems/juggler_transfer_weight_invariant.md),
[juggler_twin_flight](problems/juggler_twin_flight.md),
[juggler_two_step_parity](problems/juggler_two_step_parity.md),
[research_engine_v24](problems/research_engine_v24.md).

**Length-only charges are exhausted (added after pricing the family).** A
charge seeing only \((n,L,o)\) must bound every configuration those
numbers allow, and nothing proved forbids \(e\) valleys at
\(n,n+2,\ldots\); so it is at least \(\sim e/(n\log n)\) and the best
possible threshold is \(0.336\,q_k q_{k+1}\), against the \(0.41\)–\(0.53\)
Corollary 4.5 achieves — a ratio of \(1.21\), which is the \(6/5\) unroll
and nothing else. **Finance is the optimal length-only charge to within
the coefficient it advertises**; no sharper counting of valleys,
internals and evens is worth more than \(20\%\) in \(n_{\max}\), i.e.
\(12\%\) in period. Theorem 4.7's \(1.4048\) exceeds this only because
no-\(\mathtt{EE}\) forbids the extremal configuration. The room that
remains is *orbit-dependent* information — which is what the walk charge
reads, and why it carries the extra logarithm. Do not open another
length-only refinement.

**The trailing-evens family is not independent (added after testing it).**
`cycle_trailing_evens_lt` is the one constraint whose strength reads
\((1+1/n)^{2^r}\) rather than \(\theta\), so it looks like the
floor-sensitive lever the standing prohibition leaves open. It is not.
The window at the cut has log width \(2^r\log(1+1/n)\) and the \(r\)
square roots divide the log by exactly \(2^r\), so the transported width
is \(\log(1+1/n)\) at every \(r\): the constraint at any depth is the
\(r=1\) one carried back, and \(r=1\) is `cycle_last_even_interval`, from
which Theorem 4.4 is derived. The \((n+1)\) against \(n\) is the
granularity of the return. Do not open it as a third mechanism.

---

## Cubic-band order does not enforce actual parity

**Structural restriction retained; cycle exclusion PARK (9 September 2026).**
A primitive actual cycle with minimum m>1 and maximum M<m^3 has sorted
rank increment e, gcd(L,o)=1, and odd prefix counts ceil(k o/L).
This conditional global-order result is proved in
[cubic-band order](problems/juggler_cycle_cubic_band.md),
`J-cycle-cubic-band-order`. It does not revive the withdrawn R<27/8
alphabet or the unconditional Christoffel reduction.

**Refuted extension:** exact prescribed-branch integer closure,
coprime counts, mechanical word, extrema parity and formal expansion
are mutually inconsistent, or suffice for full parity compatibility.
At threshold b=9, the exact size-switched
loop 9,27,140,11,36,216,14,52,374,19,82,9 satisfies these listed properties
and has M<m^3, but uses the odd branch at even states 36,14,52.
It is not a Juggler cycle. The size-switched map on [b,b^3), with its
branch cut at b^2, preserves that finite interval without fixed points
for every b>=3 (`J-cycle-threshold-relaxation`), so closed integer
orbits of this relaxed map occur at arbitrarily high minima.
Full parity compatibility is absent in this example. The desired
uniform theorem that every threshold cycle has a wrong-parity state
remains unproved: this example neither proves nor refutes it. This
corrects the earlier logically reversed wording about a "parity
contradiction". The same example's 3/11 mismatch fraction also defeats
an unconditional one-third bound.

Do not infer a no-cycle theorem or parity independence from the finite
threshold survey, and do not treat the four capped large runs as escape.
The parked question is uniform intersection of every threshold cycle
with its wrong-parity set. Even that would leave actual cycles with
M>=m^3 unresolved. Members: `cycle_cubic_band`,
`J-cycle-cubic-band-order`, `J-cycle-threshold-relaxation`.


## Cubic-band continuation: rounding tolerance and lost branch constants

**Exact obstructions to weakened tests; no-cycle still PARK (9 September 2026).**
The [same canonical dossier](problems/juggler_cycle_cubic_band.md) proves
that all cycles at one threshold share a period and interlace, and gives
a uniform log-log grid bound with error at most (1-1/L) times the surplus.
These restrictions do not resolve absolute integer parity.

**Refuted weakened criterion:** correct source parity, cubic-band rank
rotation, coprime counts and one-sided power-rounding error below 2
exclude cycles at all sufficiently large minima. For every odd b>=3,
the finite parity projection R_b on odd [b,b^2] and even [b^2+1,b^3-1]
has a nontrivial cycle with R_b(x) in {J(x),J(x)-1}. The inclusion of
odd b^2 avoids a gap 3 at the seam. Whether every such cycle contains
an altered edge remains unproved, and would itself exclude actual
cubic-band cycles. Equal rotation fractions do not force equality of
maps: S_3 has (3,5,11), while R_3 has (3,5,10), both with counts (2,1).

**Refuted gap-only criterion:** exact same-branch image differences on sources >1,
correct source parity and the global rank rule suffice for no-cycle.
The map G=J-1 on odd x>=3 and G=J on evens has the exact 11-cycle
13,45,300,17,69,572,23,109,1136,33,188,13, wholly below the cube of
its minimum. All same-branch differences on sources >1 agree with those of J;
strict nearest-even smooth-gap tests survive as well. Subtraction erases
an additive constant for each branch. A successful gap argument must
recover absolute floor-cell positions or couple these offsets.

These are different maps, not counterexamples to Juggler no-cycle. The
uniform wrong-parity intersection for the exact S_b remains the question,
and the separate M>=m^3 regime remains open. New controls use only complete
S_3, S_9, S_29 graphs and one R_b orbit at b=3,9,11,29,101; the old
large caps and census were not expanded. Members:
`J-cycle-threshold-common-period`, `J-cycle-cubic-sorted-grid`,
`J-cycle-unit-perturbation`, `J-cycle-branch-offset-obstruction`.


**Consolidation update (9 September 2026).** The six cubic-band structural
results and scoped obstructions now have compiled Lean proofs, with canonical
written proofs in Paper A Section 3.10. Earlier written-only status entries
are historical. Formalization does not settle uniform absolute-cell
wrong-parity intersection; the author authorized that next question.


## Absolute floor cells: scoped outcomes, not a parity contradiction

The authorized 9 September follow-up is
[Absolute floor cells](problems/juggler_cycle_absolute_cells.md).
For every b>=3, independent pre-floor phases in [0,1/(2b^3)] leave the
entire threshold map unchanged. A strict rotation response to every
positive phase, or isolation of zero phase by these finite constraints,
is therefore unavailable. Absolute image anchors recover integer branch
constants but do not contradict zero-offset closure.

The new upper-cell/grid charge is a valid stronger necessary estimate;
it holds for threshold cycles with wrong parity as well. The tighter
extrema strips use actual parity and exact cells but leave a large region.
The altered cycle 3->5->10->3 satisfies the derived bounds and both
extrema anchors while failing the remaining odd upper cell. This refutes
the sufficiency of those consequences, not the universal wrong-parity
statement. No new floor or cap campaign is justified by these findings.

## Euclidean induction does not discard parity guards

[Exact Euclidean induction](problems/juggler_cycle_cubic_induction.md),
authorized closure gate, 9 September 2026. **PARK** the broader tactic.

**Refuted shortcut:** collapsed exact endpoint cells plus odd retained
endpoints and the threshold cuts imply the deleted source parities.
For every odd s>=3, set b=s^3. The exact threshold first return
s^4 -> s^6 -> s^3 has both endpoints odd, but the E-source s^6=b^2
is odd. These are unbounded-scale blocks, not full cycles.

Exact two-branch Euclidean recursion and the OE/OOE/OOEOE endpoint
identities survive. Faithful predicate composition still transports
every original parity check, with total expanded count L at every
stage. This counts that representation; it does not prove that all
bounded guarded representations are impossible. Fixed-word large-source
error decay does not supply a bound uniform in the changing return word.
Do not relabel the terminal full-word predicate, two named branches,
or a larger source scan as a no-cycle obstruction. Members:
cycle_cubic_induction, J-cycle-cubic-euclidean-induction,
J-cycle-cubic-return-compression, J-cycle-cubic-hidden-parity.

## Bounded cell carries do not survive the tested pure-power substitution

[Exact parity carries](problems/juggler_cycle_guard_carries.md),
9 September 2026. **CLOSE** the specified bounded additive extension.

The exact OE quotient has a clipped correction in {0,1,2}. It does not
remain such a family after replacing an eliminated source O(x) by
x^(3/2) in the next quotient. The infinite genuine OOE family with
x=r^8+8, odd r>=3, has substituted quotient error 36r^2 or 36r^2+1
and clipped displacement error 27r^2. All source parities, exact cells
and cubic-band positions are valid. The endpoint odd projection still
works, with ordinary ideal endpoint exactly one higher.

The ideal radicand lies outside the original endpoint unit cell; this
is failure of the proposed extension, not a contradiction to the exact
one-block normal form. Keep the actual source square remainder or
supply a new update identity. Unbounded correction magnitude does not
prove unbounded field count or defeat every parity formula: the family
itself has a simple polynomial correction and fixed guard parity.
Likewise known odd-cube fiber alternation defeats bounded interval or
polynomial-sign classifiers but has a mod4 rule and gives no complexity
bound on cycle-selected ranks. Do not promote either narrow obstruction
to a no-cycle theorem. Members: J-cycle-oe-quotient-parity-carry,
J-cycle-ooe-carry-substitution-obstruction, cycle_cubic_induction.

## Unbounded parameter families do not establish orbit escape

[Family chains and exact remainder transport](problems/juggler_cycle_remainder_transport.md),
9 September 2026. The specific family X(r)=r^8+8 has a growing exact
OOE block, but it cannot repeat forever as that same family: reentry
forces r=1 mod48 and every continuing transition lowers nu2(r-1) by 2.
This proves departure from the description, not descent after departure.
All six selected family starts reach 1, including large excursions;
neither these controls nor the valuation theorem settles every parameter.

Keeping the exact first square remainder repairs the old quotient
substitution at the OOE level. Do not continue describing that repaired
formula as impossible, or promote its bounded temporary register count
to uniform whole-word parity closure. The guard still requires an
initialized/certified absolute remainder, endpoint validation and
constituent guard evaluations. The aggregate composition law already
exists in GlobalDefect and its mod2 residue only reads endpoints.
Members: cycle_remainder_transport, J-cycle-ooe-family-chain-bound,
J-cycle-ooe-exact-remainder-repair.

## Exact first remainders do not repair fixed residue summaries

[Whole-word residue guard](problems/juggler_cycle_guard_residues.md),
9 September 2026. **CLOSE** the specific extension retaining an exact first
square remainder and finitely many residue classes of the source, first
image, endpoint and endpoint aggregate, even with aggregate valuation and
full common threshold/return section.

For every even Q there are two exact OOE first returns in that same geometry
with R=0, matching listed residues modulo Q and aggregate valuation 3,
yet opposite hidden E-source parity. Taking Q an even common multiple
defeats any fixed finite set of moduli. This does not include the full
absolute source, endpoint or quotient; the prior exact quotient repair
correctly distinguishes the pair. Neither source is claimed to be periodic.
Do not turn this into an impossibility theorem for all fixed-register
algorithms, all absolute-remainder summaries, or cycle-selected carries.

For odd endpoints, the length-L aggregate is source^(3^o)-1 modulo
2^(L+2); at an odd fixed point its valuation is nu2(source-1).
The residual XOR energy counts changes in mismatch status; an actual
mismatch sum still evaluates all constituent guards. Enlarging a fixed
modulus, packing the checks, or naming that sum an energy is not a new
uniform arithmetic update. Member: J-cycle-ooe-fixed-residue-obstruction.

## A periodic return seam excludes a strip, not all cycles

[Periodic carry follow-up](problems/juggler_cycle_periodic_carries.md),
9 September 2026. The positive result
J-cycle-periodic-return-height-strip gives M<m^3-m^(15/8) for actual
cycles with m>=7 and M<m^3, via a sharper exact integer ceiling.
Do not promote that excluded top strip to emptiness of the entire
cubic region, a restriction on taller cycles, or a new period floor.
The old S_9 cycle passes the extremal seam but has an even retained
base and other parity failures.

Periodic endpoint matching does not make the carry sum zero: it is
sum(peaks)-sum(base squares). Any odd base set and permutation admit
exact E suffix cells with peaks=destination^2+1; this partial model
omits the O-prefix equations and is not a cycle. Product identities
remain existing floor-defect composition. A future propagation result
must use the joint absolute cells or multiple ordered boundaries;
carry bookkeeping or another single strip is not a global proof.


## One-sided later-return error bounds cannot be uniform at a fixed minimum

The [later-return dossier](problems/juggler_cycle_later_returns.md) proves
a third finite-word contraction but also identifies the precise limit of
the sufficient certificate
2*p*m^(p-1)+1+sum(q_j*m^(q_j-1))<=2.
For a proper-prefix word and1/2<p<1 it requires
m>(2p)^(1/(1-p)), so no fixed minimum supports this certificate for a
family with p approaching1 from below, even before inner losses are added.
This is not a counterexample to the actual map contracting; signed
paired errors may admit a stronger estimate. Do not relabel a larger
one-sided sum as uniform guard closure.

The exact terminal factorization UV=P OE Q, VU=P EO Q explains another
omission: right-transfer contractions only track the common suffix Q.
The mixed OE/EO passage contracts in an actual cubic-band cycle, but
the common prefix P can amplify the gap. Its ideal exponent combines
with the mixed block and suffix to give the original product3^o/2^L>1.
An extra fictitious same-word terminal edge or an uncontrolled prefix
does not prove no-cycle. A new joint cell or absolute-loss estimate is
required; the terminal closure identity alone is a reformulation.


## Terminal joint cells: local signs and relative errors do not close the cycle

The [joint-cell gate](problems/juggler_cycle_terminal_joint_cells.md) is **PARK**.
Its new exact local obstructions rule out two shortcuts. Even with full
local source/output parities and arbitrarily large minimum, an E edge
can have floor-to-ideal gap distortion approaching 2/3 or 2. In a
separate guarded mixed family, the exact OE/EO paired loss is below
-1/2 or above r while m,h,M,t,q and their cells are held fixed.
Both families lie below the existing smooth height-excluded strips.

These are open blocks; they do not refute an inequality using complete
cyclic P/Q placement. Conversely, treating their independent remainders
as favorable, or replacing every E distortion by 1+o(1), is invalid.
The complementary-path product and unweighted remainder sum telescope
to closure and four boundary terms. A new result must constrain the
signed remainders with their actual nonconstant cyclic weights.
The identities p(P)=2p(V), p(Q)=2p(U)/3 do not prove p(V)<1.
Applying the prescribed V word at m ends with the wrong E guard and
cannot furnish an actual descent from the cycle minimum.


## Cyclic weighting does not replace the integer lattice

The [weighted-remainder gate](problems/juggler_cycle_weighted_remainders.md)
is **CLOSE** for its specified rank and real-cell averaging route.
The inverse-gap entropy sign is an identity for positive vectors under
permutation. A nonnegative cyclic Green inverse leaves signed coefficients
after the adjacent difference operator.

More strongly, at every prescribed real minimum there are complete cyclic
rank configurations satisfying all initialized strict REAL unit-width cells
and threshold placement, with constant positive logarithmic defects.
Every centered defect direction is available by small perturbation. This
gives both signs for nonconstant fixed centered weights and nonzero continuous
common-edge weights in that relaxation. The full-circle state-dependent
entropy weights are not covered by the sign-reversal claim.

Do not promote these examples to integer floor cycles: they omit parity,
may violate odd gap>=2 and DC/LR height strips, and do not refute a bound
that genuinely uses those hypotheses. Constant normalized defects also
do not make raw square remainders constant. The exact integer formula is
one positive parity jump plus a signed carry sum; matching the required
remainder-parity pattern and odd minimum merely recodes all original guards.
The fully arithmetic joint comparison remains open. A concrete next test
must impose both exact odd O-predecessors of the terminal cut states.
Members: cycle_weighted_remainders, J-cycle-real-cell-weight-obstruction.


## Exact odd cut predecessors still do not fix the mixed-loss sign

The [cut-predecessor gate](problems/juggler_cycle_cut_predecessors.md) is
**CLOSE** for its predecessor-only sign obstruction. Nonpositive loss
requires the odd integer ceiling of m^(4/3) in a shrinking O(m^(-1/6))
upper window; cube minima force positive loss. This is a conditional
sign statement, not exclusion of cycles with cube minima.

For every r>=67,r=3 mod16, the recorded polynomial family has actual
guarded paths a->O h->O M->E t and b±->O s±->E m->O q, with the same
m,h,M,t,q and b+=b-+2. It gives Delta-<-3/4 and Delta+>2r-1, while
m^3-M>2m^2 survives all current smooth height strips at their cutoffs.
The negative face realizes the thin noncube predecessor alignment.
Thus neither independent parity faces nor the two exact O predecessors
force a universal mixed-loss sign.

Do not infer full cyclic placement: no adjacency in an actual periodic
set, complete original A/B return seam, or common terminal P/Q closure
is constructed. The missing initial seam is B(t),A(m)=B(q), with all
guards and quantitative cycle constraints. Any further finite rectangle
test must either supply a new coupled restriction or record its surviving
family and stop local-prefix stacking; deleting this one parameterization
would not prove the general obstruction.
Members: cycle_cut_predecessors, J-cycle-cut-predecessor-alignment,
J-cycle-cut-predecessor-two-signs.


## Even the full initialized return seam leaves both mixed-loss signs

The [initialized-seam gate](problems/juggler_cycle_return_seam.md) is
**CLOSE** as a finite local sign obstruction. The cut-predecessor family
has an infinite refinement r=u^4+2,u=65 mod2048,u>=2^32 on which
A(a)=t,B(b±)=m,A(m)=z,B(t)=w are fully guarded for A=OOE,B=OE.
The new O outputs are even; their E outputs w,z are odd. All twelve
distinct displayed edges across the two alternative faces are exact,
with the complete numerical anchor order and both signs
Delta-<-3/4,Delta+>2r-1.

Its common gap (216u^11+1188u^7+1863u^3-3)/64 satisfies the stated
DC/LR scalar lower bounds and the mixed AB/BA upper bound without the
additive 9/8. The inherited cubic deficit is greater than 2m^2. Thus the
whole initialized rectangle, its exact cells/parities and those scalar
bounds do not force one sign. Fifteen rational polynomial certificates
and four congruence certificates prove the infinite statement; the three
fixed controls are implementation checks, not a census or existence proof.

Do not automatically append another fixed word or discard this family
and claim no-cycle. Neither alternative provides the five adjacent pairs
in an actual cycle, selected C/W transfers, counts satisfying all finance
and grid restrictions, or the simultaneous ordered A/B matching of the
same retained integer set. The concrete global question is whether some
required interval population exceeds exact guard-compatible preimage
capacity beyond the existing spacing and grid bounds. Restating the
global matching requirement alone is not a new obstruction.
Members: cycle_return_seam, J-cycle-return-seam-family.

## Mechanical words do not supply a uniform period-surplus bound

The [period-upper-bound gate](problems/juggler_cycle_period_upper_bound.md)
is **PARK** for actual cycles, not refuted. Its formal-word shortcut is
closed: infinitely many coprime pairs with the least expanding odd count
give primitive rational mechanical words with all noncontracting prefixes,
the even-endpoint envelope, initial OO and terminal EOE, but
L(o log3-L log2)>=L log3/4 tends to infinity. No integer floor cells
realize this construction. Do not confuse the rational mechanical word
with the irrational greedy hug word.

Separately, the saved S5 threshold cycle has L=14,o=9 and
L(o log3-L log2)>log3, certified by 3^125>2^196. Its exact closure and
rank rotation do not force convergent status, but eight wrong-parity
states make it inapplicable to Juggler. This one control does not refute
some larger uniform constant, even for threshold cycles.

For an actual primitive cycle the unconditional terminal-loss lower
bound and distinct-target upper budget combine only to the vacuous
lower bound L>sqrt(m^2+1)-m. A useful period upper bound still needs a
new coupling, such as L(o log3-L log2)<=C. Do not treat that hypothesis
as proved, or substitute a lower bound on m into an increasing
m-dependent upper bound to claim an absolute period cap.

The authorized parity audit gives the exact remainder interval
d<=rho<=2y-d, d=(source-target) mod2. Its switch upper loss is still
asymptotic to 1/(y log y), not to the compulsory 1/(2y^2 log y).
For every odd y>=3 the actual E edges y^2+1->y and y^2+2y-1->y
attain those two endpoints. These open edges do not refute a bound
using complete cyclic placement. The four-class parity packing formula
is a refinement of the existing budget, while the cubic grid and switch
counts give lower surplus constraints. None supplies the proposed
upper bound L Lambda<=C. Endpoint aggregate valuation is already
nu2(m-1), independently of the expanding count pair; fixed congruence
bookkeeping does not impose convergent-quality approximation.
No new count-pair theorem or further executable branch resulted.
Members: cycle_period_upper_bound, J-cycle-loglog-surplus-window,
J-cycle-period-surplus-word-obstruction.


## Raw preimage multiplicity and ordinary Hall do not supply a cycle deficit

The [preimage-capacity gate](problems/juggler_cycle_preimage_capacity.md)
is **CLOSE** for ordinary multiplicity/density/Hall counting. Capacity
must count distinct supported targets. In every surviving numerical band,
the proper singleton target (r^2+2)^3 has support size1 but at least
(r^2+3)/4 actual guarded B=OE preimages. This unbounded inflation does
not make raw counts false as necessary inequalities; it makes them weaker.

For a fixed target set and freely chosen candidate sources, deterministic
preimage fibers are disjoint. Hall reduces exactly to singleton support.
Restoring the requirement that predecessors form the same unknown Y
restores the original closure problem. The explicit shared-source/target
intersections do give necessary capacities, but no smaller-than-required
bound is proved. Guard-free inverse density recovers source spacing,
and the shared rank chains recover the existing Euclidean towers.

Exact holes are real: an A=OOE target y>=8 has at most the integer
candidate ceil(y^(8/9)); odd fourth-power sources fail its final E guard.
In the old family r^9 is a missing guarded A target inside(z,t).
Do not infer that this target must belong to Y, that the supported cube
targets satisfy the A-source guards, or that all global capacities pass.
No shared-set matching, cycle, or strict capacity deficit is constructed.
The genuinely unresolved input is a mandatory rank population exceeding
the exact shared support, beyond spacing and grid consequences; merely
writing that inequality or pruning until closure is not a new theorem.
Members: cycle_preimage_capacity, J-cycle-preimage-capacity-diagnostics.


## Cumulative prefix errors and fourth-power deletions do not force joint capacity

The authorized [joint-capacity continuation](problems/juggler_cycle_preimage_capacity.md)
retains a valid necessary bound: middle support bijects fully guarded AA
sources in[m,H], H=K(a+1)-1, and its population alpha-beta is at most
(H-m+1)/32+C5(H^(47/48)+(m-1)^(47/48)), from current Paper B's OOEOO
prefix count. The seven state parities are OOEOOEO; density1/128 for
that full event is not proved.

**CLOSE** only the specified quantitative mechanisms. If
L=o(m^(47/48)), this endpoint-subtraction upper expression exceeds L
uniformly on every nonempty source interval above m. To cover all three
imported prefixes OO,OOEO,OOEOO use L=o(m^(5/6)). This lower-bounds the
upper allowance, not the true discrepancy or support. Empty intervals,
exact holes and sharper localized estimates remain outside the claim.

Separately, in a hypothetical m,L->infinity regime with the additional
unproved uniform condition Lambda<=C0/L, the existing grid yields
a=m^(4/3+o(1)), H=m^(32/27+o(1)), and L=O_C0(m log m). Therefore
H/L->infinity, so every fixed positive whole-block allowance plus
nonnegative error eventually exceeds the entire cycle population.
These are conditional scale implications, not constructed actual cycles.

Odd fourth-power sources already fail OOEOO's third guard and must not
be subtracted again. Possible new exclusions whose first A output is
an odd fourth power have upper budget P4(A(m),A(H))-P32(m,H), at most
H^(9/32)/2+1; no positive uniform lower count is established. The source
and transported fourth-power budgets total o(H), so they cannot remove
a fixed positive whole-block leading term when H/m->infinity.
An upper deletion budget cannot be subtracted as a guaranteed deletion.

No strict joint-support deficit, numerical period/height improvement,
full-AA density or no-cycle theorem is obtained. Exact joint support
remains open; the certified floor and published period floor are unchanged.
Members: cycle_preimage_capacity, J-cycle-joint-prefix-capacity.


## Integer transport nonvanishing does not contradict closure

The authorized [integer-weight continuation](problems/juggler_cycle_weighted_remainders.md)
keeps full actual integer parity and both terminal boundaries. The lifted
positive wrap gap m^3-M gives B_i ell_sigma(i)=N_i ell_i-r_i everywhere.
Its cut correction multiplies the minimum E-source remainder by
Qs=s^2+sm^2+m^4; it is an algebraic lift, not an actual O step from even s.

All numerator factors N_i are odd; exactly two denominator factors B_i
are odd. Thus P=productN/productB differs from1, and the exact downstream
force F is nonzero, |F|>=2/productB. Its cleared numerator has valuation
nu2(ell_0). **This is compatible with closure:** F=(P-1)ell_0.
Parity does not determine which side of1 contains P or the force's sign.
The cleared congruence is a consequence of the local initialized cells.

The compulsory parity contribution is positive but the carry term is
signed. Its sharp separate-coordinate box bound is not known to force
the needed inequality. Downstream weights rise across a following E
and fall across a following O in chronological order; this does not
prove monotonicity on the sorted-rank paths. The exact carry-level
boundary sum still requires information from the shared integer states.

Integrality also forces delta_E>delta_O on every actual OE pair ending
at an odd state, and a positive difference between the logarithmic cut
and wrap gaps. This removes uniform-defect models from the integer
setting. The standard resulting entropy/variance comparison gives only
Lambda>sqrt(L/(2(L-1)))[eta(m^2)-eta(M)], weaker than the already known
compulsory loss eta(m^2). No contradictory entropy sign follows.

**CLOSE** this transport/parity/energy derivation as a new exclusion
mechanism. Retain its exact refinements; the full arithmetic carry
bound remains open, and is not refuted by a real-cell or local witness.
No period, height or floor update and no automatic next gate.
Members: cycle_weighted_remainders, J-cycle-integer-weight-refinements.


## Carry-level nesting and the OE comparison preserve the same boxes

The [carry-level continuation](problems/juggler_cycle_weighted_remainders.md)
is **CLOSE** for the tested envelope, local comparison and fixed-word
weighting shortcuts. Target carry caps strictly increase in target rank,
so their envelopes are suffixes there and circular intervals in source
rank. But nested levels inside those envelopes are exactly the original
integer boxes. Their minimizing levels are the envelopes intersected
with the negative-coefficient set, already nested and attaining the old
box minimum. An envelope need not be an occupied interval.

For any fixed increasing positive odd targets y_j, every integer carry
choice 0<=k_j<=y_j-1 is realized by ordered genuine E cells
x_j=y_j^2+1+2k_j. Individual source bounds merely clamp coordinates.
This is a free-coordinate theorem: it preserves neither shared O
predecessors nor the same downstream weights after the sources change.
Exact O inverse cells remain singleton-or-empty and cannot be replaced
by their much larger carry boxes.

Retaining the normalization and v=y^2+1+2l, the proved OE defect
contrast becomes exactly k<=v-1 at l=0 and is weaker at l>0.
It removes no points from that initialized local carry relaxation.
This does not invalidate the contrast or forbid its use with genuinely
new global constraints.

The exact spatial weight ratio is a product along u inverse-rank steps,
with the mandatory 1/P factor when it crosses the chosen time origin.
It may equivalently use the complementary v=L-u block. Since
Lambda/L<eta(m)->0 forces e/L toward an irrational limit, the inverse
congruence eu=1 mod L makes both u and v diverge along hypothetical
actual cycles with m->infinity. This needs no bound on L Lambda.
Fixed short-word contraction estimates do not establish the needed
raw coefficient signs after their signed corrections are discarded.

No actual-cycle flux bound or count/height improvement was obtained.
The next distinct target is a paired-error estimate uniform in return
depth with complete cyclic boundary placement. No larger word list,
carry census, new floor or automatic next gate is authorized here.
Members: cycle_weighted_remainders, J-cycle-integer-weight-refinements.


## Uniform signed-return cocycles retain the closure obstruction

The [uniform signed-return audit](problems/juggler_cycle_weighted_remainders.md),
Results 14–16, is **CLOSE** for the tested affine/cone/cocycle deduction.
It supplies exact identities and scoped limitations, not a counterexample
to every possible arithmetic uniform estimate.

Affine composition must evaluate each suffix on the actual image pair.
The full-word ideal-power normalization additionally has a calibration
term, nonpositive for a concave suffix and nonnegative for a convex one.
Neither a fixed input interval nor signed gap data alone supplies the
absolute image placement. Do not switch those coefficient normalizations.

For equal-length cycle arcs, repeated shared states cancel exactly.
The signed log-log discrepancy is at most Lambda, uniformly at all
induced depths. Mandatory parity charges supply explicit offsets, but
both statements use the existing gap oscillation and loss budget.
Relative control divides by the input gap; obtaining a vanishing
allowance from a grid comparison requires the unproved small L Lambda
regime. No favorable sign follows merely from the positive total loss.

The full terminal prefix, mixed passage and suffix have log-log gap
changes summing to zero. The nonnegative logarithmic endpoint-loss cone
is invariant but symmetric in its signed coordinate; at closure it gives
an elementary endpoint inequality. Normalized log-secants multiply to
exp(-Lambda), while the ordinary secants multiply to one after their
endpoint factors cancel. This is the existing exponent surplus and
closure, not an independent contraction. Raw downstream products still
contain the initialized signed square-remainder corrections, including
the lifted cut and wrap; their sign cannot be inherited from the
normalized endpoint product.

No new cycle restriction or distinct executable next mechanism was
identified. A sharper bound on residual defect imbalance over the
terminal prefix's exclusive arcs would need additional arithmetic
control from the shared odd-cube predecessors. Naming that missing
inequality, restoring full guards or increasing return depth is not
itself a new attack. No next gate is launched.
Members: cycle_weighted_remainders, J-cycle-integer-weight-refinements.


## Local quartic returns need not preserve merged order

The [quartic-band order theorem](problems/juggler_cycle_quartic_band.md)
is **PROMOTE** for its actual-cycle restrictions. Only the local
merged-monotonicity shortcut is **CLOSE**.

For every odd t>=3, at free anchor \(m_0=t^5\), the actual guarded
first returns \(F=OOE\) from \(x=t^8+8\) and \(G=OEO\) from
\(x'=t^8+10\) to the same interval
\([\lceil m_0^{4/3}\rceil,m_0^2)\) have outputs
\(t^9+9t-1>t^9\), reversing source order. All intermediate states
lie in \([m_0,m_0^4)\), with the exact floor cells and guards.
These are open paths; the anchor is not an asserted cycle minimum.
Do not infer a common cyclic matching or an unbounded orbit.

An actual cycle with m>=16 and M<m^4 instead admits an oriented
rank shuffle of displacement at most \(D=\lceil\ell^{1/4}\rceil\),
\(\ell=\lceil\lceil m^{4/3}\rceil^{4/3}\rceil\). Its inversion count
I satisfies \(d-1\le I\le\min(c,r-c)D\) and
\(I\equiv d-1\pmod2\), where d=gcd(L,o), r=o-e, and c counts high
odd states. This gives new structural and height/count restrictions,
but does not force I=0; when d=1 it only forces I even. Do not
extrapolate exact cubic rotation, a period-independent numerical
displacement, or error D after arbitrarily many iterations.

The short quartic return alphabet here is proved using an exact
lower floor margin. It does not restore the withdrawn derivation
of a factor-free alphabet from an upper power envelope.
Further restrictions would have to use shared cyclic integer cells.
No next gate is launched.
Members: cycle_quartic_band, J-cycle-quartic-return-order.


## Quartic target holes do not force a selected-cell deficit

The [shared-cell continuation](problems/juggler_cycle_quartic_band.md),
Results 8--11, is **PROMOTE**. Unlike arbitrary local guards, common
cyclic injectivity does strengthen the order theorem: inversions are
exactly earlier-F/later-G pairs in the same auxiliary OE cell. At most
one actual G uses each cell, so I<=c and gcd(L,o)<=c+1. The permitted
shuffle consists of disjoint cell-prefix rotations, whose active cuts
must connect the underlying rotation residue classes.

The local hole-to-deficit shortcut remains **CLOSE**. For a cell with
G valley v, selected F targets are odd values in (O(v),O(v+1)] and
have no odd O predecessor. Their actual predecessors are even, so
that exclusion agrees with the F guards. For v>=64, the number of
free odd target slots exceeds the number of all free odd source
candidates in the cell. This compares available parity slots, not
proved guarded F support, and yields no selected-state deficit.
Do not infer that every F must invert, that a generic missing
preimage removes an actual selected F, or that I must be zero.

The genuine open inversion family remains compatible with the
same-cell theorem. The new permutation and height restrictions
exclude neither the entire taller slab nor all d=1 possibilities.
A useful further deficit must constrain the number of actual F
sources failing to precede a G in their own cell, while retaining
the common cyclic equations. No next gate is launched.
Members: cycle_quartic_band, J-cycle-quartic-return-order.


## Quartic extremal descent does not iterate through F sources

The [nonparticipant audit](problems/juggler_cycle_quartic_band.md),
Results 12--14, leaves the c_0>=1 target **PARK**. The existing
shared-cell theorem stays PROMOTE. Only the tested extremal descent
and auxiliary full-set exponent shortcuts are **CLOSE**.

The largest F source has an actual OOEOE descent of exponent27/32
below itself, an interior state. If it participates, the shared
cell gives actual endpoints v<W<T<a<b<w<t. The internal valley
v is outside H, and W,T have no forced F labels or smaller invariant
cycle. The global maximality used for the following parity cannot
be repeated for an arbitrary smaller F source.

The minimum cell supplies its G source, not a selected F after it.
The existing open inversion family may be anchored at its listed
minimum u^6, but is not a cycle. The sole u=3 maximum-extension
control fails the next O(t) parity; its prescribed square root is
not an actual E successor. Do not use it as a guarded nested fold.

On the taller side M>=m^3, under c_0=0 the auxiliary O/B map closes on the actual low states,
but redirected F edges make it noninjective. Its c old F targets
have indegree zero. Finite closure permits transient trees; every
periodic component must contain a changed F edge. The aggregate
log-exponent identity includes
sum_F(loglog B(x)-loglog F(x))<0 from indegrees, so even a negative
total ideal exponent does not contradict the nonnegative defects.
Only a periodic component permits that term to telescope.

No positive nonparticipant bound or new count/height exclusion was
obtained. An arithmetic constraint on auxiliary periodic components
remains missing; finite closure and its sign are not that constraint.
No next gate is launched.
Members: cycle_quartic_band, J-cycle-quartic-return-order.


## An auxiliary threshold period is not an actual-cycle period

The [auxiliary component audit](problems/juggler_cycle_quartic_band.md),
Results 15--18, **PROMOTES** the conditional disjoint-block theorem.
The uniform component/one-mismatch exclusion remains **PARK**.
Only treating its threshold period or excursion identity as an
actual-cycle contradiction is **CLOSE**.

Under all participation, the auxiliary map is exactly a low-section
return of S_m. At c=d-1 its unique periodic component lifts to a
threshold cycle of period L/d with one wrong-parity high odd state.
Every other edge of that cycle is actual, but the exceptional E
edge is not. Do not apply the certified actual Juggler period floor
to L/d or infer a second component from its transient G partner.
The complementary actual excursion has exactly the defect needed
to restore the original Lambda; the decomposition alone has no
contradictory sign.

The new positive result uses a different comparison: replace
periodic altered F blocks by distinct genuine G-partner OE blocks.
These disjoint actual blocks, together with all omitted positive-loss
F towers, fit inside the original loss budget. Full cut-residue
coverage forces (e-1)Lambda>d log(3/2). Hence in the coprime
small-product regime, at least one F must be nonparticipating.
The product hypothesis is additional. A nonparticipant is not
itself a cycle contradiction, and its G may lie before it or be
absent from its cell. Do not extend the positive replacement sign
without checking that ordering and actual partner availability.
No next gate is launched.
Members: cycle_quartic_band, J-cycle-quartic-auxiliary-loss-budget.


## A late G-partner shift is not paid by its own F tower

The [covered-cell extension](problems/juggler_cycle_quartic_band.md),
Results 19--22, **PROMOTES** a conditional uncovered-cell theorem.
The proposal to absorb each negative replacement shift into that
F tower's own defect is **CLOSE**: for odd y<x, F(x)>x^(9/8)-2
and x-y>=2 imply F(x)>y^(9/8), giving the strict opposite sign.
The open family y=t^8+6, x=t^8+8 for odd t>=3 has all late-pair
guards. It supplies no cyclic closure or unconditional obstruction.

The abstract-order shortcut of forcing an early periodic F is
also **CLOSE**. The fixed e=12, r=9, s=3 control in Result 22
has a primitive actual-form permutation, correct branch growth,
and only one periodic F under full-cell collapse; that F is late.
Inversion cuts must not be confused with full collapse cuts.

The valid comparison retains signed genuine-block substitution.
Exact cell width bounds each negative shift by eta(m), and each
periodic late F has positive integer collapse displacement, so
q_minus<=N Delta. Together they yield the conditional criterion
(e-1)Lambda+e eta(m)<=log(3/2) for d=1, forcing an uncovered F.
The hypothesis is not established uniformly. Its missing B value
can lie outside Y while the actual F tower still returns inside
the cycle. Vacancy alone is not a no-cycle proof; the across-cell
replacement question remains PARK. No next gate is launched.
Members: cycle_quartic_band, J-cycle-quartic-covered-cell-budget.


## The coarse neighboring-cell gap bound is automatic

The [neighboring-cell continuation](problems/juggler_cycle_quartic_band.md),
Results 23--26, **PROMOTES** the conditional component witness.
Every predecessor-projected component must contain an uncovered F
under the same condition as Q43; each has a normalized gap >tau.
The following two shortcuts are **CLOSE**, while a uniform
arithmetic bound on the actual witness intervals remains **PARK**.

Replacing the missing partner by a preceding selected G moves the
target valley from v to u<v. The small two-endpoint OE defect
difference does not bound the projected source substitution:
the boundary z(v)-z(u) is added to projected finance and cancels
when the genuine source block is substituted. Dropping it loses
the vacant-cell cost. The projection may have a lower fixed point;
allow n=1,p=0 and do not identify it with an exact threshold cycle.

The maximum selected-valley gap Omega satisfies the formal
necessary condition (e-1)Lambda+e Omega>log(3/2), but that is
already forced by old counts and span. With C=log(4/3), g=r-c,
one has Omega>=C/g and eC=r log(3/2)-Lambda. If Lambda<=c log(3/2),
then e Omega>=log(3/2); otherwise (e-1)Lambda>log(3/2) since c>=1.
Thus the coarse maximum-gap condition adds no arithmetic restriction.

The valid witness theorem uses each component's own partner
intervals and their rank displacements. The fixed e=7 control has
an uncovered F only in a transient path and satisfies the prior
global existence conclusion, but is excluded by the new component
condition at the stated small-product hypothesis. It is abstract,
not a floor-realized cycle. No global no-cycle conclusion follows.
Members: cycle_quartic_band, J-cycle-quartic-component-gap-witness.


## Bare quartic gap transport preserves the witness

The [quartic transport continuation](problems/juggler_cycle_quartic_band.md),
Results 27--29, PROMOTES complete selected-cell separation under the
existing coprime small-product condition. It does not obtain the proposed
upper gap bound from transport alone. For a negative F/G substitution,
source gap = target gap + delta_F - delta_G. Replacing the source gap
in component finance cancels exactly those omitted F losses; the positive
G-partner losses remain. Thus the target also has a normalized witness
above tau. Repeated endpoint transport does not create an opposite sign.

At the existing e=7,r=5,s=2 control, the pure rotation and predecessor
collapse (0,0,0,3,4,5,6), with both F ranks 1,2 uncovered, have a fixed
projected component {2}. The real potential z_i=z0+i*A/7+h_i,
h_i=(Lambda/100)*1_(i=2 mod7), and defects Lambda/7+h_i-h_(i+2)
are strictly ordered and strictly positive but nonconstant. Every lifted
length-two normalized gap is at least A/7-Lambda/200, above
tau=A/7-3Lambda/7. This is not an integer-floor or parity realization
and does not meet or refute the published period floor.

Therefore the bare transport-to-upper-bound shortcut is CLOSE. This does
not close the separate arithmetic realization problem. Sorting the actual
power envelopes supplies a valid positive rotation defect; its minimum
gap excludes every repeated B cell under Q43. That new restriction still
allows all F valleys to be unselected. A further attack must use absolute
shared integer endpoints beyond the already satisfied real cocycle.
Members: cycle_quartic_band, J-cycle-quartic-separated-cells.


## Separated minimum cells do not force an auxiliary image to be selected

The [absolute quartic continuation](problems/juggler_cycle_quartic_band.md),
Results 30--33, PROMOTES strict re-entry localization: under Q43 a strict
missing F valley's O image can return to H only at the preceding F target,
through consecutive valleys whose later value is at most 2m. This is not
an exclusion of strict missing images; above that window they escape H
while the actual F return still closes in the original cycle.

The local shortcut from a selected minimum-G anchor, exact guards,
distinct B cells and log-log spacing to selected auxiliary images is CLOSE.
For every odd t>=3 the exact open paths in Q78 have m=t^6-4,
G source t^8-4t^2-2 and F source t^8+8. Their B values are m and t^6;
all four displayed section states have distinct cells and circular gaps
greater than eta(m). The F valley t^6 and its O image t^9 are both absent.
No outgoing returns from the two endpoints, cyclic count equations, or
full actual cycle are asserted. The tempting G source t^8-4t^2 fails
its guard: its first O image is odd. The corrected -2 source is essential.

Adjoining every missing F valley closes the enlarged O/B set iff all
F=G endpoints agree. The threshold cycle then has the same period,
branch counts and total loss as the original, with explicit wrong high
odd E guards and any even inserted O guards. It gives no surplus gain.
In the strict case adding more images changes counts without a proved
preserved-loss relation. Neither finite-completion shortcut proves no-cycle.

The exact small path 9->27->140->11 has F=G, so full local F guards alone
do not imply strictness for every source. It does not address a large
minimum. For v>=8, equality forces the unique source ceil(v^(4/3));
the full large-valley cell/parity test was open at that gate. The later
unbounded equality family in quartic Result 36 resolves the local
existence question positively, while periodic membership remains open.
Re-grouping the known even-to-odd charges eta(v^2) by quartic tower type
does not supply a new signed residual estimate. Absolute cycle exclusion
remains PARK; no raised floor, full cycle, or divergent orbit is claimed.
Members: cycle_quartic_band, J-cycle-quartic-absolute-reentry.


## Guarded OOE/OEO endpoint equality is not eventually strict

The [shared-remainder gate](problems/juggler_cycle_quartic_band.md),
Result 36, closes eventual local F>G from the complete actual F guards
and a large auxiliary valley alone. For every t>=8192 with t=9 modulo16,
the Q90 polynomials give an actual odd/odd/even/odd path x->h->p->q,
with B(x)=v=t^6-3t^2+6 and O(v)=q. Ten exact polynomial margin
certificates prove the floor identities uniformly as v tends to infinity.
The auxiliary valley v is even, so its alternative O edge is prescribed.
This is endpoint equality with full F guards, not an actual G path.

There is no selected minimum-G anchor, full return partition, Q43 count
condition or periodic membership in this family. It neither constructs
the all-equality actual-cycle case of Q74 nor refutes a global strictness
theorem with those additional hypotheses. Fixed large examples are
controls; the infinite claim rests on the polynomial proof.

The same gate closes the tested aggregate remainder elimination route:
sums, products and the modulo16 target-eighth-power identity in Q89
repeat the exact matching hypothesis. They are not an additional
independent signed obstruction. This does not close stronger coupling.

A genuine positive result survives: the shared OE cube equation forbids
both odd remainders being one modulo7. Q84 gives an additional positive
charge; Q87--Q88 strictly tighten the signed interval for whole actual
return blocks. This is stronger than merely regrouping old compulsory
charges, but supplies no orientation. An arc cutting a pair cannot be
assigned its entire correction without boundary accounting. No-cycle
stays PARK; no floor or paper release changes.
Members: cycle_quartic_band, J-cycle-quartic-coupled-remainder,
J-cycle-quartic-unbounded-equality.


## Located OE charges account for terminal boundaries but give no net loss

The [cut-pair continuation](problems/juggler_cycle_quartic_band.md),
Results 37--39, PROMOTES a charge located on the incoming O leg and
the general support bound Q96. A classical Gaussian factorization
excludes x^3=p^2+1 for positive even p, so the O remainder is at least
three independently of the E edge. The earlier modulo7 joint-corner
lemma is valid but is not an irreducible two-edge interaction. Its
comparison baseline was the old separate parity bounds.

The exact path 847->24650->157 has E remainder one and zero E excess
above that baseline. It is a finite open control, not a large-minimum
family or periodic example. No symmetric R=1 counterpart exists.
The older raw OE dominance is CW25 and is already implied by the
initialized upper boxes, as proved at CW35.

Reserve kappa(p) on the O leg and only D(v)-kappa(p) on its pair's
remaining residual. Charging both kappa and the full D would double
count. The resulting bound works for arbitrary original-edge arcs.
In the actual cubic terminal placement, P and mixed split exactly
the same m-landing pair as (+1,0) and (0,+1), while Q contains it
whole as (-1,-1). Both ends of each signed interval improve, but
the coefficient vectors sum to zero on every edge. Optimizing their
remaining losses independently cannot create three simultaneously
realized positive charges. This boundary-only net-loss shortcut is CLOSE.

The formal support inequalities concern supplied residual records;
the Gaussian and complete actual-cycle assembly remain written.
The cubic terminal table is not an original quartic rank-rotation
theorem. No-cycle orientation stays PARK; no floor or paper release
changes and no new executable mechanism follows from this gate.
Members: cycle_quartic_band, cycle_weighted_remainders,
J-cycle-quartic-boundary-loss.

## OOE escape: full arithmetic families and shifted-state valuations

[OOE escape families](problems/juggler_ooe_escape_families.md), 10 September
2026. Every nonempty eventual odd residue class contains a source with even
O(x), so fixed source congruences cannot certify an all-OOE invariant set.
A full nonlinear polynomial value tail misses one return in every late
triple of parameters. Finite unions of full nonlinear polynomial tails
also fail closure, even with arbitrary target parameters, by the integer
finite-difference and finite-coloring argument. Linear tails fail the guard.
Do not read these full-family obstructions as exclusion of a sparse orbit.
Polynomial update templates are separately limited by a decrease of at
least three in nu2(state-polynomial degree); that argument does not cover
nonpolynomial updates or infinitely many templates.

The proposed uniform ranks nu2(x-1), nu2(x+1), and nu2(x-9) are **REFUTED**.
The exact actual return 199->2807->148718->385 increases the first rank
from 1 to 7. The known X(r)=r^8+8 parameter-chain valuation remains valid
with its original family hypotheses. Arbitrarily large finite blocks,
bounded replay maxima, and family departure do not prove or refute one
escaping trajectory. Rows J-ooe-escape-residue-obstruction,
J-ooe-escape-polynomial-obstruction and J-ooe-escape-shifted-valuation.

## Cubic first-rank curvature: total-loss transfer does not force parity

[Rank curvature and signed floor loss](problems/juggler_cycle_rank_curvature.md),
10 September 2026, **CLOSE**. The full-polynomial-tail finite-difference
obstruction cannot simply be imposed on arbitrary sorted cycle states.
The exact inverse-rank defect simplex and the ideal log-log grid allow
ordered odd triples with curvature 0 and 2 at the fixed formal tuple
(L,o,e,m)=(780239,492276,287963,350000001), with an ordered real extension.
The ideal curvature about 0.282233 therefore supplies no contradiction
under those relaxed assumptions. These are outward interval controls,
not an actual cycle or a model satisfying every upper floor cap. The chosen
m itself fails the odd-image condition, as O(m)=6547900454916 is even.

Row J-cycle-rank-curvature-window is REPARAMETERIZATION: the exact target
H_0(c1)<chi<H_2(c1) is the gap 0<c2-2c1+m<2 expressed through signed actual
floor losses. A closed-box capacity formula is recorded, but its full
target-dependent group sums are not evaluated. The cap into m exceeds the
negative clearance in this fixed diagnostic; this is not a proof of
independent variability or global feasibility with all actual cells.
Do not reopen bare grid width, odd spacing, or the total budget as a new
parity exclusion. A new result must retain the common selected integer
states and prove a stronger signed estimate. That actual-cell question
remains open; no no-cycle theorem or improved period bound is claimed.

### Complete cap-envelope continuation of the cubic curvature gate

[The same canonical record](problems/juggler_cycle_rank_curvature.md),
Results 6--9, now evaluates all three target-envelope capacities at the
fixed first surviving count pair. Their rigorous total is about 4.778e-6,
leaving a signed interval about plus/minus 1.307e-6. Including the CW44
compulsory charges and parity-refined independent upper caps changes
either endpoint by less than 9.714e-13. More accurate integration of
these same envelopes cannot put that interval inside the 1e-10 curvature
window. **CLOSE** this cap-envelope test, row
J-cycle-rank-capacity-envelope. The earlier real ordered control and the
new capped aggregate control are different relaxations; do not claim one
configuration satisfies their union or all actual integer cells.

The actual Q/R cap totals themselves differ by epsilon in (0,eta(m)),
because their targets are adjacent paired ranks. But chi=-epsilon+s_R-s_Q
depends on the signed unused upper-cell slack, whose exact integer
complement is (y+1)^2-x^h. Elimination of those remainders recovers existing
transport; closeness of cap totals does not orient used losses. The
shared-state integer comparison remains open. The total-cap/log-squared
argument was already registered in J-cycle-absolute-cell-grid-charge;
do not rebrand it as new finance. Its checked m<520000000 corollary at
these counts narrows a cubic minimum range only, without killing the
period, raising the descent floor, or excluding the taller regime.

### Actual upper-square complements: three scoped global shortcuts

[The canonical curvature record](problems/juggler_cycle_rank_curvature.md),
Results 10--13, consolidates the symbolic continuation. **CLOSE** the
following tested inferences, without claiming that every arithmetic use
of the common integer cells must fail:

- Complete paired-arc slack products have identical branch factors and
  cancel to the old endpoint curvature identity. Ratios of logarithms are
  not rational integer products; switching to raw rational factors loses
  the source normalization needed for the signed log-log statistic.
- Eliminating the auxiliary complements from their definitions alone
  leaves a free state polynomial ring. A fully linked modular projection
  also respects parity and the elementary complement boxes, but not the
  exact integer cells, grid or total loss. Its unbounded minima violate
  known finance at fixed counts. It is not a countermodel in the surviving
  minimum range, and does not rule out state-dependent precision methods.
- The exact balanced rotation indicator bounds the desired signed sum by
  actual first or second variation. It supplies no small variation bound
  or oriented sign. Shared integer secants have two competing terms.

The retained local theorem J-odd-image-upper-square-gap is Lean verified:
an actual odd-to-odd edge has upper-square complement at least three.
Its written cap-shave estimate, added to prior corrections, changes an
endpoint by less than 1.62e-12, far below the existing clearance exceeding
1.303e-6. Do not promote this local improvement as a no-cycle mechanism.
The weighted frequency and magnitude of normalized complement increases
remains an unresolved input, with no new period exclusion or floor change.

### Whole-word upper-slack compensation is the same refined cap

[Rank-curvature Result 14](problems/juggler_cycle_rank_curvature.md)
retains the actual odd predecessors and every genuine OE/OOE block in
the complete paired word. Its normalized gap differences telescope.
The OO upper-square gap supplies a positive paired baseline b, but the
residual r=s-b is exactly V-delta, with V=eta-b. This is an affine
bijection with the already tested refined-cap box, including the total
loss and known coordinate charges. **CLOSE** this independent-charge
propagation: adding the baseline again after shaving the cap would
double count it. No false global counterexample is inferred from free
local E cells or box endpoints; a stronger inequality from exact shared
integer secants remains unproved.

## Shared secant quantization does not orient normalized slack

The next [rank-curvature audit](problems/juggler_cycle_rank_curvature.md),
Result 15, is **CLOSE** for the gap/gcd-only sign inference and automatic
strict or global three-point convexity transfer. It does not close the actual shared-state
problem. For paired genuine same-branch edges with positive even gaps
d,D and g=gcd(d,D), the exact change satisfies
Delta U=d modulo 2g. The normalized increase condition gives the
lattice-rounded rational threshold RC44, a necessary test with no supplied
global bound on the selected positive variation. The mod-eight sum leaves
branch-weighted interior gaps; the open paired arcs cannot be assigned
zero total complement difference.

For every odd t>=9, the actual OO edges from t^2-4,t^2,t^2+4 have odd
images t^3-6t,t^3,t^3+6t. Both adjacent pairs have source gap4,
target gap6t, and gcd2, yet their normalized upper-slack differences
have opposite signs. RC46--RC48 prove the cells and both signs uniformly.
This is an unbounded family of local triples, not a cycle or a claim of
cycle adjacency. It refutes orientation from these gap data, not a
nonlocal bound retaining absolute cycle placement.

Three-point secant transport is the difference of two paired equations
and retains the unknown complement second difference. Its global log-log
lift still telescopes, and synchronized triples cross mixed-parity and
wrap positions. No new period, height, or minimum restriction is obtained.
The conditional lattice test and written family are retained without a
new production Lean module, source census, or PDF work.
Members: cycle_rank_curvature.

## Exact OO edges do not force a fixed local cap fraction

[Rank-curvature Result 17](problems/juggler_cycle_rank_curvature.md)
closes a positive universal local compensation fraction, even for genuine
OOE first returns with zero initial OO loss. For every c>0 and height H,
there are square starts x=t^2>H with actual guarded chain
t^2 -> t^3 -> floor(t^(9/2)) -> floor(t^(9/4)), parities O,O,E,O,
and x<z<u<x^2<=v<x^3. The first loss is zero; each later log-log loss
is positive and less than c times its own target cap. The total loss is
therefore less than c times the sum of all three caps.

The construction uses joint equidistribution of two smooth powers along
odd t and an exact nested-square-root identity. Epsilon is fixed before
t tends to infinity; no shrinking-target rate is established. The
explicit genuine OE family b^4+2 -> b^6+3b^2 -> b^3, for odd b>=3,
also has both cap-normalized losses tending to zero.

These are individual finite blocks at arbitrarily large heights, not a
cycle, a concatenation theorem, or an escaping orbit. This result does
not refute the smaller height-dependent integer charges or a bound that
requires simultaneous selection by a complete cycle. Positivity at the
parity changes cannot alone be promoted to a fixed fraction of the caps.

ReturnCells formally verifies the square-start fourth-power cell and
its guarded actual-chain adapter. Equidistribution, infinitude, and the
analytic loss bounds remain a written AI-assisted proof with independent
human review outstanding. Two fixed integer controls, found by bounded
parameter searches and replayed exactly, illustrate rather than prove
infinitude. No orbit census or certified-floor increase follows.
Members: cycle_rank_curvature.

## More ranks do not automatically improve absolute-cell precision

[Rank-curvature Result 16](problems/juggler_cycle_rank_curvature.md)
closes the tested rank-polynomial determinant and rearrangement-only
inferences. The determinant with columns 1,j,...,j^(r-1),z_j is
the product of factorials times the r-th finite difference. Its lattice
divisibility and its independent error radius acquire the same factor.
It therefore adds no precision to the previous grid test; this is not
a claim about every determinant involving actual source/target cells.

The existing Lean theorem cube_fiber_sqrt_odd already gives the exact
parallel OO edges k^4+4j -> k^6+6k^2j for odd k>=3 and 0<=3j<=k.
All states are odd and every higher rank difference vanishes on a long
enough window. These are arbitrarily long finite collections of single
edges, not consecutive orbit times or a full-grid cycle realization.
Do not repackage this known affine-cell mechanism as a new family result.

The squared matching cost has the wrong global Monge sign across the
cubic branch cut. Putting even-source radicands before odd-source cubes
restores the inequality, whose optimum is exactly the known rank rotation.
The log-log state moment is the existing finance identity. No other
useful moment comparison is established by this audit.

Nor do wrong-parity points next to a periodic edge imply cycle coverage.
For an even periodic upper source x with odd target y in a threshold map,
both x-1 and y^2 are wrong upper states in the same square cell. Periodic
injectivity forces them to be transient. A compatible cycle would have
at least e distinct wrong transients of the first form. This is conditional
and supplies no compatible cycle. The full shared absolute-cell problem
remains open; no new restriction, census, Lean module, or PDF work follows.
Members: cycle_rank_curvature.

## Complete cell propagation needs an effective exhaustion argument

[Rank-curvature Result 18](problems/juggler_cycle_rank_curvature.md)
parks the bounded complete-cell campaign. Unlike independent cap boxes,
exact forward and backward lower-endpoint contractors cannot stabilize
at a false solution: opposite root inequalities force every actual edge
on the same vector, and sortedness plus coprime rank rotation gives a
primitive cycle. Finite valid upper bounds ensure eventual exhaustion
or a solution under fair updates. This standard completeness argument
supplies no useful runtime bound or no-cycle theorem.

Four full sweeps at (L,o,e)=(780239,492276,287963), with outward grid
initialization and no parameter subdivision, retain every domain nonempty.
The minimum bracket narrows only to 350000005..519999995. The lower
endpoints fail the exact-cycle check; this is neither a fixed point nor
a cycle witness. Four odd endpoint values are trimmed in this fixed
cubic model, without a count-pair exclusion or a certified-floor change.

The independent-remainder modular shortcut is saturated when
Q/gcd(2,Q)<=m0-1. At m0=350000001 this includes every even Q<=700000000.
Use the least common multiple when several moduli constrain one remainder.
The statement does not cover narrowed jointly coupled remainders, exact
integer difference equations or additional finance constraints. Residues
may accelerate the complete algorithm but are unnecessary for correctness.
Neither larger generic machinery nor extra unfinished sweeps establish
the missing efficient arithmetic obstruction. PDFs are unchanged.
Members: cycle_rank_curvature.

## Automatic crossing payment does not add a new defect budget

[Rank-curvature Result 19](problems/juggler_cycle_rank_curvature.md)
closes the automatic coarea payment mechanism. Each selected nonwrapping
slack rise is already bounded by the preceding target's actual defect.
For fixed caps, signed slack differences are linear in the old defect
coordinates; crossing identities hold for every feasible vector in the
old cap simplex. They alone cannot eliminate its optimizers.

Raw complement levels also have target-dependent logarithmic cost, and
the circular cap jump is nonzero. Three fixed genuine parallel OO edges
45->301, 49->343, 95->925 refute paying the entire middle slack rise from
the next downcrossing edge's actual defect on those local ordered cells.
This does not assert their membership in one cycle or refute every
subdivided crossing assignment using additional cycle arithmetic.

A new global valuation argument does survive: every actual cubic cycle
satisfies L<=(H+1)(3+2S), where S counts deviations from any chosen
three typewise raw remainder constants and H is the maximum lifted-gap
2-adic valuation. At the fixed tuple S>=4483; choosing block minima
forces at least 8966 raw excess units. This supplies neither their
location nor the weighted size needed by the signed criterion. Do not
promote a support count alone to a no-cycle theorem. The full-cycle
assembly remains a written AI-assisted proof; Lean verifies its
conditional arithmetic/counting kernels. Independent human review is
outstanding.
Members: cycle_rank_curvature.

## Splitting total remainder support does not locate signed loss

[Rank-curvature Result 20](problems/juggler_cycle_rank_curvature.md)
successfully merges critical valuation transport, even-pair divisibility,
mechanical itinerary counts and the common lifted-gap budget. It raises
the fixed deviation bound to 7284 and forces at least 14569 critical
corrections. These events are not simply all nonzero corrections.

The separate support-only signed fusion is closed. For any union A of
rank/type/height bins, knowing S>=s0 alone gives only at least
max(0,s0-|A complement|) deviations in A. At the fixed counts all 7284
can fit in a source-type intersection with the neutral signed group,
while retaining distance at least 7284 from every three-constant profile.
This is a support relaxation, not a common-cell realization or a claim
that the complete new critical-run constraints permit that placement.

Exact remainder-to-defect integration gives a valid unsigned lower bound
using the 7284 smallest target weights. The mandatory first two raw units
at those locations cost less than 5e-15 in total; this additional minimum
charge alone does not close the old signed-cap clearance above 1e-6.
Actual excesses can be larger, and the unknown block-minimum baseline
must not be equated with the old universal compulsory-charge budget.
Further amplitude, placement or coupling is required. No cycle class
is excluded, and no PDF work was performed.
Members: cycle_rank_curvature.

## Critical-event localization still does not orient paired slack

[Rank-curvature Result 21](problems/juggler_cycle_rank_curvature.md)
adds information omitted by the earlier support-only projection:
absolute rank ceilings force blocks of at most 21 even-gap vertices,
and each 21-source window in R meets a critical event. Disjoint pairing
with Q forces at least 14380 deviations in Q union R, so an all-neutral
placement is excluded under these full hypotheses. The earlier neutral
construction remains valid at its explicitly weaker support-only scope.

Criticality by itself still does not choose the helpful normalized
sign. The exact Result 15 family t^2-4,t^2,t^2+4, for odd t>=9, maps
on genuine OO cells to t^3-6t,t^3,t^3+6t. Both source gaps have
valuation two, as do the nonzero corrections -4(3t^2-16) and
4(3t^2+16). Yet the two normalized paired slack signs are opposite.
This closes that local sign inference; the cells are not claimed to
belong to a cycle. Unequal raw remainders also cannot automatically
be identified with unequal normalized defects at different targets.

The actual selected-pair theorem is a positive localization result.
A signed estimate using the complete simultaneous cycle constraints
remains open. No count pair is excluded and no PDF was rebuilt.
Members: cycle_rank_curvature.

## Critical correction cost and Boolean windows need joint arithmetic

[Rank-curvature Result 22](problems/juggler_cycle_rank_curvature.md)
closes a charge growing solely with valuation restoration. The exact
O pairs 4s^2-1,4s^2+1 map to 8s^3-3s,8s^3+3s, with critical correction
two and arbitrarily large restoration on the even-s OE subsequence.
Their next E endpoints collide or cannot both be odd, so this control
does not satisfy distinct complete returns. A symmetric generalization
does pay normalized O cost greater than 1/23 when its complete guarded
returns are distinct, under the stated family and parameter hypotheses.

However, the existing RC61 family b^4+2 -> b^6+3b^2 -> b^3 at distinct
odd b<c gives critical O correction 3(c^4-b^4), distinct guarded OE
returns and normalized losses tending to zero along c=b+2. It fits a
common cubic band, but does not assert cycle membership or adjacency.
The fixed scale's adjacent log-log gap bound actually rules out two
of these quartic source values as consecutive ranks. These different
controls must not be combined into a fictitious full-cycle witness.

The critical-window condition alone also leaves the shared mod-4
marginal relaxation unchanged: ordinary gaps can all have valuation
one, making every R event critical. Every saved marginal interval
supports that pattern, but it is not a nonlinear cell solution. Only
eight domain samples and aggregate widths were saved; no full-domain
pruning claim follows. Further complete-cell elimination remains PARK,
with no added sweep or minimum subdivision in this gate.
Members: cycle_rank_curvature, J-cubic-critical-cost-compatibility,
J-cubic-critical-cost-kernels.

## Complete critical OOE pairs still have no uniform local charge

[Rank-curvature Result 23](problems/juggler_cycle_rank_curvature.md)
extends the cheap critical OO pair 4s^2-1,4s^2+1 through two genuine
distinct OOE returns for arbitrarily large odd parameters selected by
four simultaneous smooth phases. The initial correction is exactly two,
all six cap-normalized losses can be arbitrarily small, and all states
fit a common cubic band. All four ordinary pair log-log gaps also tend
to zero. Thus criticality, exact OOE guards, injectivity, a shared cubic
band and isolated positive gap ceilings do not force a uniform charge.
This is a written four-phase derivative/Weyl argument; its infinitude
and real estimates are not Lean verified and still need human review.

The conclusion does not assert a parameter hit within the fixed minimum
interval, a full sorted rank vector, simultaneous cyclic selection of
many pairs, or one infinite orbit. Exact finite square-start counting
forces at least 53034 positive first O remainders among the first 83650
cycle ranks, but the displayed loss lower bound is below 10^-26 while
the fixed surplus is above 3*10^-6. A positive count is not the missing
signed or aggregate loss estimate. That complete-cycle question is PARK.
Members: cycle_rank_curvature, J-cubic-critical-ooe-pair-obstruction,
J-cubic-ooe-square-start-packing.

## Sparse paired OOE sets and narrow fixed-base power tubes fail invariance

[OOE escape families, Sections 5--7](problems/juggler_ooe_escape_families.md)
records the attempted sparse invariant construction from a fixed seed.
No such collection was found. A subset of {4t^2±1: t odd} that contains
both signs at a parameter s>=5 cannot be A-invariant: the two return
values differ by more than two but less than the spacing between distinct
template parameters. This applies to arbitrarily sparse paired selections,
and does not exclude a one-sided selection. Both tested seeds 1599840003
and 1599840005 return outside the template and then have even O images;
each completes one OOE block only. Their later actual fates were not tested.

For any fixed real base c>1 and logarithmic tube width 0<=epsilon<1/17,
no infinite prescribed OOE tail can stay within epsilon of integer
log_c exponents. Above the explicit positive-exponent threshold, the
endpoint error forces 8e=9d and v2(e)+3=v2(d). Thus a finite k-step
segment in those tubes satisfies 3k<=v2(d_start). Arbitrarily sparse
exponents and nonpolynomial updates do not avoid the restriction.
Fixed additive errors from fixed-base powers, or relative errors tending
to zero, are included. Wider tubes or varying bases are not excluded.

Exact inverse cells and arbitrarily deep moving-seed constructions do
not supply a common ordinary integer. A uniform finite initial seed set
surviving every depth would suffice, but has not been proved. The nested
odd congruence classes x=(4^n-1)/3 mod 4^n illustrate that compatible
finite witnesses can have no common nonnegative integer. This is a
compactness countermodel, not an actual OOE counterexample. The general
sparse invariant-set construction remains PARK, with no escape proof.
Members: ooe_escape_families, J-ooe-escape-sparse-pair-obstruction,
J-ooe-escape-power-tube-obstruction.

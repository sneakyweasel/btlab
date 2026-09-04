# Documentation map

The documentation records exact mathematics, bounded computations, open
questions, and literature comparisons separately. Claim labels have the same
meaning throughout:

- **EXACT — HUMAN PROOF**: supported by an argument in the mathematical record;
- **EXACT — LEAN VERIFIED**: the same statement has a compiled Lean proof;
- **COMPUTATIONALLY VERIFIED**: checked on a stated finite domain;
- **CONJECTURE**: open and paired with counterexample search;
- **OBSERVATION**: empirical, without necessity or universality;
- **REFUTED**: a counterexample is recorded;
- **REPARAMETERIZATION**: a classical construction under a local name.

These seven are the only tags allowed in
[theory/theorem_ledger.json](theory/theorem_ledger.json) and in research
notes. Do not write **PROVED** or **VERIFIED COMPUTATIONALLY**.

A halt theorem, a “no cycle of any length” theorem, or a Collatz/Juggler
solution slogan is overclaim unless the English is covered by
**EXACT — LEAN VERIFIED** (compiled, no `sorry`, Lean matches English)
or **EXACT — HUMAN PROOF**. Weaker compiled lemmas — period floors,
densities, leftover censuses, finite certificates — do not unlock those
phrases. If the covering statement exists, name the theorem with its
quantifiers and Lean name; do not hide it under “this is not a halt
theorem,” and do not replace it with “we solved Juggler / Collatz.”

Novelty is a separate axis, used in dossiers and theory pages and never
as a ledger tag: **KNOWN** (in the literature, cite a `literature/` id),
**PROJECT-SPECIFIC** (what this project measures or refines), and
**OPEN** (no proof and no refutation yet). **REPARAMETERIZATION** sits on
both axes. See [methodology.md](methodology.md).

## Start here

The live publication task is the Juggler programme.

1. [Paper A — cycle-length lower bounds](theory/juggler_finite_dynamics_note.md)
2. [Paper B — parity discrepancy](theory/juggler_parity_discrepancy_note.md)
3. [Branch ledger](juggler_branch_ledger.md)
4. [Negative knowledge](negative_knowledge.md) — every recorded
   `REFUTED` / CLOSE / method wall, clustered by killing invariant
5. Reviewer snapshot: [juggler_review/](../juggler_review/)
   (export only; edit the `docs/theory/` sources, then rebuild)

The rewrite-calculus note remains ready to send
([draft](theory/rewrite_calculus_note.md),
[reviewer packet](theory/rewrite_calculus_reviewer_packet.md)).

Last promoted BT-core theory (STRUCTURAL; parked; no new monomial strata):

1. [Balanced-ternary calculus](theory/balanced_ternary_calculus.md)
2. [Cubic Newton stratum](theory/cubic_newton_stratum.md)
3. [Residual versus classical sources](theory/residual_vs_classical.md)
4. [Theorem ledger](theory/theorem_ledger.md)

Foundation, then operators: [mathematics.md](mathematics.md),
[balanced_ternary_operators.md](balanced_ternary_operators.md).
Collatz is a parked application: [collatz_mathematics.md](collatz_mathematics.md).
Method: [methodology.md](methodology.md).

## Foundations

- [Balanced-ternary mathematics](mathematics.md): canonical representation,
  arithmetic, metrics, and residue invariants.
- [Operators](balanced_ternary_operators.md): shift, negation, digit
  derivative, reversal, and the integer/word interface.
- [Operator algebra](operator_algebra.md): compositions and commutators.
- [Finite-state maps](balanced_ternary_automata.md): which arithmetic maps
  are sequential transductions.
- [Additive combinatorics](balanced_ternary_additive_combinatorics.md):
  digit-restricted sumsets and carry defect.
- [Polynomials](balanced_ternary_polynomials.md): \(P_n(x)\) with
  \(P_n(3)=n\).

## Calculus and rewrite

- [Balanced-ternary calculus](theory/balanced_ternary_calculus.md)
- [Trit algebra](theory/trit_algebra.md)
- [Digit derivative](theory/digit_derivative.md)
- [Rewrite calculus](theory/rewrite_calculus.md)
- [Rewrite-calculus paper note](theory/rewrite_calculus_note.md)
- [Rewrite-calculus reviewer packet](theory/rewrite_calculus_reviewer_packet.md)
- [Rewrite-calculus formalization gate](theory/rewrite_calculus_formalization.md)
- [Trit control](theory/trit_control.md)
- [Setun connection](theory/setun_connection.md)
- [Normalization](theory/balanced_ternary_normalization.md),
  [rewrite system](theory/normalization_rewrite_system.md),
  [complexity](theory/normalization_complexity.md),
  [Setun normalization](theory/setun_normalization.md)
- [Jets](theory/balanced_ternary_jets.md),
  [polynomial jet calculus](theory/polynomial_jet_calculus.md),
  [jet transducers](theory/jet_transducers.md)
- [Residual-state complexity](theory/residual_state_complexity.md)
- [Quadratic residual complexity](theory/quadratic_residual_complexity.md)
- [Polynomial function congruence](theory/polynomial_function_congruence.md)
- [3-adic lifting trees](theory/padic_lifting_trees.md)
- [Minimal lifting state](theory/lifting_state_complexity.md)
- [Local vs global root-count bounds](theory/local_vs_global_stabilization.md)
- [Residual explorer](tools/residual_explorer.md)

## Newton stratum

Canonical cubic record: [cubic_newton_stratum.md](theory/cubic_newton_stratum.md).
Short extract: [newton_stratum_note.md](theory/newton_stratum_note.md).
Classical comparison: [residual_vs_classical.md](theory/residual_vs_classical.md).

Historical layer notes (stubs that point at the monograph):
[image](theory/cubic_residual_image.md),
[fibres](theory/cubic_residual_fibres.md),
[deepest layer](theory/cubic_deepest_layer.md),
[intermediate layer](theory/cubic_intermediate_layer.md),
[depth-deficit 2](theory/cubic_deficit_two.md),
[N1 valuation](theory/cubic_n1_valuation.md),
[N0 reduction](theory/cubic_n0_reduction.md),
[mismatched quotient](theory/mismatched_cubic_quotient.md).

## Juggler application

The active research application. No halt theorem is in the present
record. That is a status line, not a ban on stating a later matching
`EXACT` theorem.

- [Paper A](theory/juggler_finite_dynamics_note.md): itinerary
  obstructions, finance, walk-charge envelope, certified floors
- [Paper B](theory/juggler_parity_discrepancy_note.md): parity
  discrepancy of nested floor powers; certified descent density \(7/8\)
- [Flight extract](theory/juggler_flight_note.md) (descriptively terminal)
- [Cycle finance note](theory/juggler_cycle_finance_note.md)
- [Walk-charge note](theory/juggler_walk_charge_note.md)
- [Paper D draft: near-convergents of log 2 / log 3](theory/juggler_near_convergent_diophantine_note.md) (family leftover; not a fourth review object)
- [Itinerary-structure note](theory/juggler_cycle_itinerary_structure_note.md)
- [Branch ledger](juggler_branch_ledger.md)
- [Negative knowledge](negative_knowledge.md)
- Problem dossier: [juggler_sequence.md](problems/juggler_sequence.md)
- Lean spine: [architecture/juggler_lean_spine.md](architecture/juggler_lean_spine.md)

## Collatz application

- [Collatz mathematics](collatz_mathematics.md): consolidated exact record
  for the accelerated odd-only map.
- [Research questions](collatz_research_questions.md): answered questions,
  open targets, conjectures, and preserved counterexamples.
- [Itinerary compatibility](collatz_itinerary_compatibility.md)
- [Zero-lift dynamics](collatz_zero_lift.md)
- [Dual coding](collatz_dual_coding.md)
- [Affine-center geometry](collatz_affine_center.md)
- [Fixed-integer asymptotics](collatz_fixed_integer_asymptotics.md)
- [Cycle languages](collatz_cycle_languages.md)
- [BT word maps](collatz_bt_warp.md)
- [Literature comparison](literature_comparison.md)
- [Balanced ternary versus Collatz literature](balanced_ternary_vs_collatz_literature.md)
- [Cycle literature comparison](cycle_literature_comparison.md)
- [Cycle literature replication](cycle_literature_replication.md)

## Problem dossiers

Each dossier follows [problems/TEMPLATE.md](problems/TEMPLATE.md).

- [Juggler sequence](problems/juggler_sequence.md)
- [Rewrite calculus](problems/rewrite_calculus.md)
- [D/Add residual completion](problems/d_add_residual.md)
- [Signed-digit residual phase transitions](problems/signed_digit_residual.md)
- [Signed-digit residual geometry](problems/signed_digit_residual_geometry.md)
- [Signed-digit residual minimality](problems/signed_digit_residual_minimality.md)
- [Signed-digit constrained controls](problems/signed_digit_constrained_controls.md)
- [Signed-digit short-horizon controls](problems/signed_digit_short_horizon.md)
- [Multiplicative residual universality](problems/multiplicative_residual.md)
- [Balanced-ternary finite-state dynamics](problems/balanced_ternary_finite_state_dynamics.md)
- [Residuals](problems/residuals.md)
- [Collatz](problems/collatz.md)
- [Shortcut Collatz finite descent](problems/collatz_finite_descent.md)
- [Ostrowski order-m adder](problems/ostrowski_order_m_adder.md)
- [Regular-output preimages](problems/regular_output_preimages.md)
- [Unrestricted residual complexity](problems/residual_complexity.md)
- [Monna endpoint spectra](problems/monna_endpoint_spectra.md)
- [Lifting trees](problems/lifting.md)
- [Additive combinatorics](problems/additive_combinatorics.md)
- [Perfect powers](problems/perfect_powers.md)
- [Primes](problems/primes.md)
- [Prime residual complexity](problems/prime_residual_complexity.md)
- [Sparse polynomials](problems/sparse_polynomials.md)
- [Operator dynamics](problems/operator_dynamics.md)
- [Operator-dynamics v2 benchmark](problems/operator_dynamics_benchmark.md)
- [Balanced-ternary digit-sum dynamics](problems/balanced_ternary_digit_sum_dynamics.md)
- [Balanced-ternary weight dynamics](problems/balanced_ternary_weight_dynamics.md)
- [Balanced-ternary weight-drift dynamics](problems/balanced_ternary_weight_drift.md)
- [Balanced digit sums of nonlinear polynomial values](problems/balanced_digit_sum_polynomials.md)
- [Erdős distinct subset sums](problems/erdos_distinct_subset_sums.md)
- [k-abelian complexity](problems/kabelian_complexity.md)
- [3-adic polynomial dynamics](problems/padic_dynamics.md)
- [Local vs global root-count bounds](problems/stabilization.md)
- [Černý residual-quotient gate](problems/cerny_bt.md)
- [Misere-quotient finite-context gate](problems/misere_quotients.md)

Journal: [research_journal.md](research_journal.md).
Ledger: [theory/theorem_ledger.md](theory/theorem_ledger.md).
Negative knowledge: [negative_knowledge.md](negative_knowledge.md).
Monna spectra theory: [theory/monna_endpoint_spectra.md](theory/monna_endpoint_spectra.md).
Regular-output preimages: [theory/regular_output_preimages.md](theory/regular_output_preimages.md).

## Architecture

Laboratory layout under [docs/architecture/](architecture/overview.md):

- [Overview](architecture/overview.md)
- [Core](architecture/core.md)
- [Research modules](architecture/research_modules.md)
- [Experiments](architecture/experiments.md)
- [Conjectures](architecture/conjectures.md)
- [Formalization](architecture/formalization.md)
- [Literature](architecture/literature.md)

## Formal verification

See [the Lean project](../formal/README.md) for theorem names, build
instructions, and the boundary between abstract formal statements and Python
implementations.

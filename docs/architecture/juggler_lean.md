# Juggler Lean interfaces

The canonical sources are in `formal/Problems/Juggler/`. The publication target
is `Problems.JugglerPaper`; `Problems.Juggler` also builds laboratory work.
The ordered source inventory and the publication module list live in
`src/research/juggler_sequence/lean_paths.py`. Other historical or paper-specific
sources have explicit auxiliary roles there. The barrel imports are checked
against that inventory.

## Elementary cells and word statistics

`Dynamics` defines the actual parity-dependent map. `RootCells` supplies the
prescribed odd branch and exact nested-square-root cells without importing
cycle or fate theory. `NumericBridge` contains conversions between natural,
integer, and real cell inequalities with the required sign conditions.
`LogCells` contains the scalar logarithmic cell capacity and its bounds.

`Itinerary` records actual guards and images. `ItineraryStats` owns the odd and
even letter counts and the branch exponents. Published declaration names are
preserved when their source module changes. Clients should import the lowest
module that provides their required facts.

## Prescribed words and actual traces

`ReturnWordLoss.eval` applies a prescribed word regardless of its parity
guards. Its equality with the actual `image` requires `follows`.
Generic word exponents, loss budgets, intermediate-state bounds, and
certificate interfaces belong below the particular words and numerical
certificates in `ReturnWordData` and `ReturnWordBounds`.

Composition must retain the actual input to every next block. An ideal
exponent or an endpoint estimate alone does not establish the lower bound
at each intermediate state. Signed real or integer differences should be
converted to natural subtraction only after the relevant order is proved.

## Cycles and return sections

`CubicReturn.PeriodicExtrema` permits a bounded closed set of periodic states.
It need not be one orbit. `CycleMin` permits a closed itinerary whose length
is a multiple of the least period. The sharp primitive grid and coprimality
results therefore require a distinct-state cycle and connectedness explicitly.

`RankedReturn` is the lightweight ordered, guarded return model. Section
coverage is separate: a prefix-section witness connects its ranks to the
original periodic set. A finite transfer certificate records the indexed
words, ordered odd endpoints, guards, and endpoint equations. Existing
convenience theorems retain their published signatures.

The model is three fields: the ranked values increase strictly below `a + b`,
each of the lower `a` ranks follows `U` to rank `i + b`, and each of the upper
`b` ranks follows `V` back to rank `i - a`. `RankedReturn.min_le` anchors rank
zero as the minimum. Its induction is Euclidean rather than one step at a
time. `RankedReturn.left` reduces the pair to `a - b` and `b` on the words `U`
and `U ++ V`, `RankedReturn.right` reduces it to `a` and `b - a` on `U ++ V`
and `V`, and both carry the actual guards forward, not only the rank
arithmetic. `RankedReturn.seam` and `RankedReturn.left_seam` give the boundary
transitions at each stage, and `RankedReturn.odd_seam_gap` widens the seam gap
to two when every ranked value is odd. The terminal equal-rank case is
`RankedReturn.equality_fixes` and `RankedReturn.equality_removes_upper`: the
final restriction keeps the lower seam point and drops the upper one.
`RankedReturn.force_two_left` and `RankedReturn.force_three_left` are the
quotient-forcing steps, where supplied descent on two or three concatenated
copies together with growth on the next copy pins the quotient between two and
three, or between three and four, and returns the reduced model.
`RankedReturn.primitive_terminal_of_totals` carries coprime length and
odd-count totals to a primitive one-one model with the same totals, and
`RankedReturn.terminal_actual_factorization` factorises that primitive pair
with the parity of both images made explicit. Consumers reach these as
projections on a binder, so a lexical scan of the sources attributes none of
them; the orphan gate reports the whole group for that reason alone.

The induced word-count determinant, conserved counts, and the decreasing
sum of positive section counts support the primitive terminal construction.
`ReturnTerminal.periodicOrbit_terminal_cut` connects global adjacency and
the mixed cut using the original section witness; adjacency within an
arbitrary retained list is insufficient. Its `TerminalCut` record retains
the complete guarded prefix, mixed passage and suffix.
Neither that construction nor a finite chain of decreasing gaps provides an
unlimited chain of contractions or controls the complete common prefix.

`ReturnSeams.PeriodicOrbitModel` is the shared sorted witness for an ordinary
orbit. It retains its positive distinct-state count, ordered states, exact
successor permutation, connectedness, both directions of orbit coverage, and
minimum/maximum anchors. Pass this same model to the charge and terminal
interfaces so that their counts refer to the same states. The supplied return
time may repeat the least period; its positivity and actual return equation
are retained in the model, not just a bound on the coverage window.

`ReturnTerminal.TerminalOrbitCut` retains the full terminal geometry together
with the total lengths and odd/even counts of its two induced return words.
Those totals match the shared model's length and parity-filter cardinalities;
its length is identified with the true least period. The terminal words are
not assigned the possibly repeated length of the input itinerary.

## Grid bounds and absolute upper cells

`CubicGrid` contains the finite-cycle coboundary algebra. `CubicLogGrid`
connects it to logarithmic cell defects and sorted rank coordinates.
`RealizedGridBounds` records quantitative conclusions; it does not replace
the exact upper-cell, integrality, or primitive-cycle hypotheses.

Its conclusions are a nested conjunction, and every component has a name.
`RealizedGridBounds.surplus_pos` is positivity of the surplus;
`RealizedGridBounds.grid_bound` bounds each logarithmic grid error by the
surplus scaled by one minus the reciprocal length, and
`RealizedGridBounds.error_oscillation` bounds any difference of two errors by
the same quantity. On the gaps, `RealizedGridBounds.gap_pos` is positivity,
`RealizedGridBounds.gap_range` bounds the spread of any two gaps by the
surplus, and `RealizedGridBounds.gap_mean_bound` places each gap within the
scaled surplus of the mean. `RealizedGridBounds.log_state_lower` converts the
grid bound into a lower bound on the logarithm of each state, given that every
state exceeds one. The corresponding upper-cell accessors are
`FullUpperCellChargeBounds.scale_pos`,
`FullUpperCellChargeBounds.surplus_pos`,
`FullUpperCellChargeBounds.finite_geometric` and
`FullUpperCellChargeBounds.closed_geometric`, and the three cutoff methods are
`FullUpperCellChargeBounds.minimum_lt_of_nonlinear_cutoff`,
`FullUpperCellChargeBounds.minimum_lt_of_finiteGeometric_cutoff` and
`FullUpperCellChargeBounds.minimum_lt_of_closedGeometric_cutoff`. Both records
share basenames with `OrbitUpperChargeCertificate`, so the qualified spelling
above is the only one that identifies them; an unqualified `surplus_pos` or
`minimum_lt_of_nonlinear_cutoff` names two declarations at once.

`CubicUpperCells` combines the strict upper cell with the grid. Finite sums,
their geometric majorants, and the closed scalar consequence are separate
interfaces. A numerical cutoff or an asymptotic consequence requires its own
certificate or limit argument. In particular, a bound valid also for
wrong-parity threshold cycles is not a parity obstruction.

`CubicOrbitCharge` connects ordinary actual orbits and minimum-based closed
itineraries to the grid and charge, with the length explicitly normalized
to the least period. This extraction layer is separate from the analytic
kernel and its exact cell premises.

`CubicGrid.OrbitUpperChargeCertificate` preserves the shared orbit model, its
rank rotation and coprimality, and `FullUpperCellChargeBounds`, including the
exact finite nonlinear charge before the geometric relaxation.
`orbitModel_upper_charge` returns equality of the projected base with the
supplied model. The older grid/charge conclusions remain projections for
existing clients. The stronger finite estimate still requires the strict upper
cells; it does not infer them from the lower-cell grid alone.

`CubicChargeMonotonicity` proves that all three bounds decrease with the
minimum when the primitive length and odd count are fixed. Its cutoff methods
consume the same orbit certificate and turn a supplied bound at `m0 > 1` into
`m < m0`. Numerical evaluation of that supplied comparison is a separate
obligation. The interface consumer also checks this passage when the counts
are supplied as terminal-word totals.

## Laboratory ideal-cycle model

`IdealCycleMin` names the bead model of a `CycleMin` word and `IdealLollipop`
names what the companion's lollipop figure is allowed to paint. Neither is a
research branch, so neither has a dossier or a ledger row; both are wrappers
over existing cycle theorems, and the wrapping is what keeps a picture from
claiming more than the theorems do. `CyclePosition` sits alongside them as the
`CycleItinerary`-based general layer. The reader's entry is
[the ideal-cycle model](juggler_ideal_cycle_model.md), which walks the schema
and names the facts pinning each mark. Both modules belong to the laboratory
barrel and to no paper barrel.

## Laboratory parity support for Paper B Section 6

`DepthFourFive` declares into the `Juggler.DepthFourFive` namespace rather than
`Problems.Juggler`, is laboratory-only, and is in no paper module list. It
contains no analytic estimate. Section 6 carries Paper B's headline density
results and is the part the release record marks as postdating the proof
audit; every constant it prints is rational arithmetic on top of one Taylor
expansion, so this module checks that arithmetic rather than asking a reader
to.

Step B's depth-four identity is `DepthFourFive.stepB_structure`, the
elimination that turns the cube minus three halves of the intermediate product
into the printed two-term form. The two coefficient blocks are then shown to
be Taylor polynomials rather than an ad hoc fit:
`DepthFourFive.stepB_m_block_is_taylor` matches the m-block against the
degree-two expansion of minus one half of `(1 + e) ^ (9/4)`, and
`DepthFourFive.stepB_v_block_is_taylor` matches the v-block against three
halves of `(1 + e) ^ (3/4)`. That is why the expansion is exact at the base
point and why its error is of order `n ^ (-9/8)`.
`DepthFourFive.stepE_S_bound` covers Step E's collision-band budget, checking
that both the sharp `65` and the rounder printed `80` dominate sixty times the
`1095/1024` anchor.

Theorem 6.3's mixed `OOEO` branch is checked constant by constant.
`DepthFourFive.lemma62_exponents` is Lemma 6.2's exponent bookkeeping;
`DepthFourFive.oeoe_C_net` is the residual sawtooth coefficient that survives
the window expansion; `DepthFourFive.oeoe_window_curvature` is its
window-centre curvature `216/1024`; `DepthFourFive.oeoe_leading_coefficient`
and `DepthFourFive.oeoe_leading_curvature` are the leading mode and its
curvature `-297/1024`; and `DepthFourFive.oeoe_composite_nonzero` is the
composite `-81/1024` together with its nonvanishing, which is what makes the
curvature single-signed and Lemma 3.3 applicable. Corollary 6.4's density is
`DepthFourFive.cor64_density`.

## Publication audit and maintenance

Paper A's [formalization map](../theory/juggler_finite_dynamics_formalization.md)
identifies the precise published claims and their remaining written parts.
Its [build guide](../theory/PAPER_A_BUILD.md) defines the canonical manuscript
and generated copies.

The citation audit resolves full declaration identities. A short name is
accepted only when it is unambiguous; duplicate basenames are never resolved
by filesystem order. Reachability compares full module names. Source indexing
is distinct from proof checking: the executable Lean dependency audit checks
the exact resolved constants and the permitted logical dependencies.

The shared identifier scanner follows the regular identifier characters of the
pinned Lean toolchain, including subscripts, question marks and apostrophes.
It rejects unsupported namespace syntax rather than assigning declarations
to the wrong namespace. Escaped identifiers and generated declarations require
the Lean environment; the source index is not a complete Lean parser.
Paper A's dependency gate checks every reported dependency and permits the
recorded native scan dependency only on its two named consumers. Missing,
duplicate and unparsed records fail the gate.

The warning gate recognizes both newly built and replayed diagnostics, scopes
them to the Juggler sources and checks excess warnings before considering a
skip. The existing warning budget remains two.

After moving a declaration, preserve its public name, repair any ledger file
pointer, register new modules, compile the changed sources, and run the
default Lake build and full fast pytest suite, respecting any explicit user
restriction on PDF checks. Run the slow suite before a release. Regenerate the
explicit dependency audit when the cited set changes.
PDF rebuilding and whole-PDF validation require an explicit user request;
ordinary Lean/source work leaves the existing PDFs as the last built snapshot.
That pin reaches prose as well as Lean. `docs/theory/paper_a_release.json`
records a SHA-256 for three markdown inputs -- the Paper A note, its reviewer
packet, and the formalization map -- so a sentence added to any of them fails
`test_paper_release_gates` until the manuscript is rebuilt. Documentation
about a laboratory module therefore belongs in this note or in a dossier, not
in the formalization map, unless a republish is already intended.
The release manifest includes the source-indexing audit tool and transitive
local proof sources, so a relevant refactor cannot silently retain a stale
publication package.

The orphan gate reads current qualified declarations and identifier-aware
references. It conservatively reports ambiguous methods as unresolved lexical
candidates; it is not a dead-code proof. Generated inventories are not
accepted as usage evidence. Since 18 September 2026 the bound is a share of
the live inventory rather than an absolute count, held as two integers and
compared by cross-multiplication, so formalising more mathematics cannot fail
it on its own. It stands at 1000/10000, reset to that level by the repository
owner the same day; the share measured after the ideal-cycle, ranked-return,
upper-cell and depth-four clusters were documented is 287 of 5168, or
5.55 percent. The discipline is a ratchet:
lower the share when a cluster clears, never raise it to go green, and only
the owner resets the level.
[The gate dossier](../problems/juggler_orphan_declaration_gate.md) carries the
calibration history and the compiled-dependency review behind it.

A declaration whose basename is shared with another namespace cannot be
credited by its short name. The gate reports such a token in its ambiguous set
rather than crediting every match, so documentation that means to cite one of
them must spell enough of the namespace to disambiguate. That is not a
scanner defect to route around: two declarations really do answer to that
name, and prose naming only the basename does not tell a reader which.

## Laboratory remainder variation

The laboratory-only module CubicRemainderVariation connects a positive
zero-correction gap equation with odd numerator and even denominator to
a strict drop of the 2-adic valuation. Its finite-permutation counting
interface separates reset support from adjacency in source rank.
The conditional arithmetic consumer combines that drop with a supplied
three-boundary deviation cover. It does not yet extract the gaps,
parity facts or support cover from an actual cubic cycle.
[Rank-curvature Result 19](../problems/juggler_cycle_rank_curvature.md)
owns that written application and the precise scope of the fixed
4483-deviation consequence. This module belongs to the laboratory barrel,
outside the current Paper A publication module list.

The companion laboratory module CubicConstraintFusion retains the full
denominator valuation cost whenever a signed correction is not critical.
It supplies even-pair divisibility and weighted finite-path transport,
with block-cost and numerical consumers for the merged size budget.
Its explicit hypotheses separate local arithmetic from extraction of a
complete cycle partition. Result 20 in the same dossier owns that
written assembly; it remains outside Paper A's publication module list.

The laboratory module CubicCriticalLocation consumes explicit positive
integer gap ceilings, finite rank paths and suffix valuation costs to
prove the 21-vertex block bound at the fixed counts. Its finite cover
adapters give C>=37155, T>=37157 and S>=18577. Generic disjoint-window
and disjoint-pair kernels retain the premises needed to localize at
least 14380 deviations. An interval-filtered accessor preserves actual
R-arc membership. The two real scalar ceilings, actual block extraction
and selected-pair identification are the written Result 21 proof; the
module does not claim a full cycle wrapper or a normalized sign bound.
It belongs only to the laboratory barrel, outside PAPER_MODULES.

CriticalCostKernel completes the binary criticality test to an exact
iff for positive products with odd numerator. Its E-cell separation
interface consumes only the two square-cell halves, parities and output
order needed for the inequality. The symmetric-family consumer derives
the raw cost from those supplied cells; quartic_family_gap supplies the
integer side of the RC61 adjacency obstruction. The subsequent
consolidation preserves the four original signatures, reuses the existing
noncritical valuation budget and separates square-cell geometry from
polynomial cost. Actual Nat.sqrt consumers supply their own cell witnesses;
the stronger polynomial conclusion includes the cubic correction bound
and the denominator comparison needed for the written 1/23 estimate.
The unit-offset family now has exact O outputs and remainder identities
proved in Lean. The equal-gap OO triple `oo_equal_gap_triple` adds the
integer Result 15 family (cells, remainders, complements and raw signs);
RC48 remains written. Logarithmic normalization, four-phase equidistribution,
infinitude and complete cycle extraction remain written in Results 22--23.
The module is laboratory-only and outside PAPER_MODULES.

CubicRemainderAssembly is the laboratory wrapper from an actual
OrbitUpperChargeCertificate to lifted gaps, remainders and the ordinary
RC68 difference. Leftover m<520000000 gives H<=86. Result 19's RC70/RC71
consumers and Result 20's runCost count still take an even-denominator
cover or supplied block costs as hypotheses. The module is not in
PAPER_MODULES and claims no missing cycle or floor change.

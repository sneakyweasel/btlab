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
The release manifest includes the source-indexing audit tool and transitive
local proof sources, so a relevant refactor cannot silently retain a stale
publication package.

The orphan gate reads current qualified declarations and identifier-aware
references. It conservatively reports ambiguous methods as unresolved lexical
candidates; it is not a dead-code proof. The 11 September 2026 repair exposes 411
candidates against the unchanged 285 budget. A separate fresh Lean reference
audit resolves 43 uses and leaves 368 for review, so the hygiene cap currently
fails even though the proof and dependency checks pass. Generated inventories
are not accepted as usage evidence.

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
proved in Lean. Logarithmic normalization, four-phase equidistribution,
infinitude and complete cycle extraction remain written in Results 22--23.
The eight-declaration module is laboratory-only and outside PAPER_MODULES.

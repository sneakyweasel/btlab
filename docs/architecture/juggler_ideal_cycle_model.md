# The laboratory ideal-cycle model

Two Lean modules stand behind the companion's lollipop figure:
[IdealCycleMin.lean](../../formal/Problems/Juggler/IdealCycleMin.lean), which
names the bead model of a `CycleMin` word, and
[IdealLollipop.lean](../../formal/Problems/Juggler/IdealLollipop.lean), which
names what the drawing may paint. Together they are 245 public declarations,
reached from the laboratory barrel `Problems.Juggler` and from no paper
barrel; inside the pair, the lollipop imports the bead model. They reprove
nothing: every mathematical statement here is a wrapper over an existing
`CycleMin`, arrival or certificate theorem, and the point of the wrapper is
that a picture cannot then claim more than the theorems do.

This page is the reader's entry to those two modules. They belong to no
research branch, so they appear in no dossier and in no row of the theorem
ledger, and until this page existed the only account of them was their own
module docstrings. The consumers are `web/juggler-companion/src/juggler/`
and `web/juggler-companion/src/content/idealDecisions.ts`, which carries the
per-mark citations shown in the companion's own interface.

Nothing below is a halt theorem, a period floor, or a claim that a nontrivial
cycle exists. The only compiled cycle in either module is the sink.

## 1. The bead model

`CycleMinShape` is the combinatorial residue of `CycleMin`: at least four
evens, at least seven odds, length at least eleven, a start of two odds, an
even last letter, a last odd run of at most one, and the expansion inequality
`2 ^ length < 3 ^ oddCount`. A word may inhabit the shape without being a
cycle, which is the whole reason the shape is a separate definition, and
`cycleMin_inhabits_shape` is the only direction that holds.

Three facts about a genuine `CycleMin` are recorded here rather than assumed
by the figure. `cycleMin_valley_is_odd` says the minimum of a cycle is odd,
which the word-only shape cannot see. `cycleMin_last_odd_run_mem` produces
the witnessed decomposition behind the last-odd-run bound: a prefix, at most
one odd, and the final even, with the prefix empty or itself ending even.
`cycle_has_cycleMin` is the rotation statement: every cycle itinerary of a
start at least two has some rotation whose base point is the cycle minimum,
so working at the minimum costs no generality.

Beads carry parities and count bounds. `BeadParity.ofBranch` sends a letter to
its parity and `beadParity_ofBranch_matches` checks that the result matches
the letter it came from, which is what makes `unknown` safe to use for
interval and stem beads only. A `CountBound` is a minimum with an optional
maximum, and its predicate form is pinned by `CountBound.admitsProp_onePlus`
for the one-or-more slot and `CountBound.admitsProp_exactly` for a fixed
count, alongside the already-cited zero-plus and zero-or-one cases.

### Sure links

`sureBeadParities` is the six sure letters in reading order, the launch `OO`
then four sure `E`, and `sureBeadParities_length` fixes that count at six.
`sure_beads_known_parity` is the guarantee the figure needs: no sure bead is
painted `unknown`.

`cycleEdges` is the cyclic edge list, one edge after each sure bead, with
index five wrapping to the launch. `cycleEdges_length` ties it to the bead
list, `cycleEdges_OO_sure` and `cycleEdges_wrap_sure` identify the two sure
ends, and `sure_link_count` states the consequence the drawing depends on:
exactly two of the six edges are sure. The other four are named individually
so that no reader has to infer them by elimination, as
`launch_to_firstE_not_sure`, `firstE_to_secondE_not_sure`,
`extraEven_edge_not_sure` and `lastOdd_edge_not_sure`. An edge that is not
sure is an interval whose length is unknown, not an adjacency that has been
ruled out.

### Run form and interval slots

`assembleOddEvenRuns` builds a word from its odd-run lengths.
`assembleOddEvenRuns_singleton` is the base case, one run followed by its
even, and `assembleOddEvenRuns_eq_nil` is the emptiness criterion that keeps
the induction honest.

Four statements convert `CycleMin` into the slots the figure paints.
`cycleMin_a1_interval` gives the opening run of `k + 2` odds and one even, so
the extras after the sure launch are a zero-plus slot;
`cycleMin_last_interval` gives the closing run of `k` odds and one even with
`k` at most one; `cycleMin_realizes_sure_links` reads off the two sure
adjacencies as head, second letter and last letter; and
`cycleMin_lastEven_ne_odd_sq` records that the prefix before the final even
does not land on the square of the minimum, which is why the last even is a
closure cell and not an overshoot.

### Balloon stations

`BalloonStation` is the user-interface alphabet: sure letters and interval
slots, with no unknown-letter bead. `balloonStation_cases` is the exhaustive
case split, `balloonStation_forced_iff` characterises the forced stations as
exactly the launch and the sure evens, and `interval_station_not_forced`
names the four interval stations that are therefore not forced.
`sure_mem_balloonSchemaForced` places the launch and the first, middle and
last sure evens in the forced list, and `no_forced_station_outside_sure` is
the converse guard: a station outside that list is never forced.

The quantitative slot data is `last_odd_interval_bounds`, the zero-or-one
window on the final odd run, and `extra_even_interval_min_zero`, the
extra-even slot with minimum zero and no maximum. `balloonSchema_slots` is
the full projection of the schema onto bead slots, and `sureLaunch_two_odds`
fixes the launch station as exactly two sure odds.

### Necklace fills

A `NecklaceFill` assigns lengths to the four open edges.
`necklaceFill_unplaced_odd_budget` says the odds beyond the sure launch are
exactly the three open odd slots, and `necklaceFill_extra_even_budget` says
the evens beyond four are exactly the extra-even slot; together they are the
accounting that stops a fill from inventing letters.
`NecklaceFill.toRuns_length` gives the run-list projection its length, four
plus the extra evens. A general `CycleMin` run list need not be a fill.

### Leftovers, and what they are for

The leftovers are shape inhabitants that do not close, and they are the
evidence that the shape is strictly weaker than `CycleMin`. Each is given
twice, once as a fill and once as a word, with the two identified:
`leftover_O7EEEE_fill_admits` and `leftover_O7EEEE_fill_eq` for the word whose
seven odds all precede its four evens, `leftover_O6EEEOE_fill_admits` and
`leftover_O6EEEOE_fill_eq` for the one that spends its seventh odd between the
third and fourth even, with `leftover_O6EEEOE_eq` spelling that word out
letter by letter. Both carry seven odds and four evens. `leftover_O6EEEOE_not_cycle` and
`leftover_one_three_eee_not_cycleMin` are the non-closure halves.
`leftover_O7EEEE_ee_window` and `leftover_O6EEEOE_oe_window` exhibit one
leftover in each of the two legal 2+2 seam windows, which is why forced
isolated `OE` is not a shape law.

The necklace pin misses are the counterexamples behind the `REFUTED` verdict
on `J-cyclemin-necklace`. `necklacePinMiss2005_eq` and
`necklacePinMiss3004_eq` identify the two words with their fills,
`necklacePinMiss2005_not_admit` and `necklacePinMiss3004_not_admit` show
neither fill is admissible, and `necklace_pin_misses_oddCount_seven` records
that both carry seven odds, so the failure is the last odd run and not a
count.

## 2. What the figure may paint

`FigureMark` is the five-valued paint: forced, optional, unknown, leftover,
off-figure. `CycleFigure` assigns one to each geometric claim, and
`schematicCycleFigure` is the default assignment.
`schematicCycleFigure_forced_launch` pins the launch `OO` as forced and
`schematicCycleFigure_shape_leftover` pins the shape-is-not-a-cycle mark as
leftover, so the default drawing cannot be read as asserting a cycle.
`cycleFigure_of_cycleMin` is the discharge: from a real `CycleMin` the figure
obtains the shape together with the two-odd start, the even last letter, the
four evens, the seven odds and the length eleven.

### Join sites

A join site is a vertex of the figure, and `SureLetterSite` enumerates the
six sure letters plus a realized extra letter. Its four projections are the
display contract: `SureLetterSite.vertexParity` is the parity painted at the
vertex, `SureLetterSite.rigidity` says whether the arrival is rigid or
depends on the fill, `SureLetterSite.isValley` marks the single valley, and
`SureLetterSite.cutForbiddens` lists the rotations forbidden at that site.
`JoinFigure` carries a site together with its resolved data, and repeats the
same four projections as `JoinFigure.vertexParity`, `JoinFigure.rigidity`,
`JoinFigure.isValley` and `JoinFigure.cutForbiddens`.

Those eight are reached in proofs only as projections on a binder, which is
why a lexical scan of the sources finds no use of them. The names are load
bearing all the same: the companion mirrors this exact contract in
TypeScript, and a renamed projection is a silently wrong figure.

`sureLetterJoinTable` is the table of all six joins and
`sureLetterJoinTable_length` fixes its size. The individual entries are
stated rather than computed at the call site: `join_valley_rigid_e`,
`join_launchO_rigid_o` and `join_firstE_rigid_o` are the three rigid
arrivals; `join_oArrival_terminal_even` says the stem terminal is even at
both rigid O-sites; `join_eArrival_terminal_unknown` and
`join_fill_terminal_unknown` say the valley, third E, middle E and last E
leave the terminal unknown; `join_valley_isValley` and
`join_launchO_not_valley` separate the valley from the launch; and
`join_launchO_cut_OE` and `join_firstE_cut_even` are the two
forbidden-cut entries. `oArrival_stem_terminal_even` and
`eArrival_stem_terminal_unknown` are the underlying `stemTerminalOf` values.

`empty_interval_not_join_stop` is the rule that keeps empty intervals off the
drawing: an unforced station contributes no sure letter.
`assembleFill_thirdE_lt` bounds the schema index of the third sure `E` inside
the assembled word, which is what makes the third-E convention well posed.

### Stem

The optional stem is not the cartoon `OOE`. `defaultStem_not_sure_OOE` says
the default stem slots are not that triple, and `stemKind_not_balloonSchema`
says the stem is not the cycle schema wearing different paint.

### Witness

A figure may carry a `RealizedWitness`, and the default does not:
`schematicLollipop_no_witness` says the witness is absent and
`schematicLollipop_join_valley` says the default join is the valley. The only
compiled cycle witness is the sink, stated three ways, as
`compiledCycleWitness_is_cycle`, `compiledCycleWitness_is_one`, and the
banner `figure_compiled_cycle_is_sink`, which asserts together that the start
is one, that the word is a `CycleMin` there, and that the schematic figure
carries no witness.

The inhabited stems are finite and explicit. `evenTowerThree_n` fixes the
start at two raised to two raised to two, and `evenTowerThree_capture` is its
capture onto one; `stem_descent_two` is finite progress at two;
`walkOf3_reachesOne`,
`walkOf3_witness` and `walkOf3_not_cycleMin` are the walk from three, which
reaches one and is not a cycle minimum. `sink_collision_stem_even` and
`sink_seam_is_oArrival_join` identify the sink seam as an O-arrival join with
an even stem parent. `leftoverO7EEEE_witness_shape` and
`leftoverO7EEEE_witness_not_cycle` are the leftover witness: shaped, and not
a cycle itinerary at any start. `necklace_pin_misses_off_shape` puts the two
pin misses outside the shape entirely.

## 3. What the model does not claim

The schema is a projection of the run list onto six sure letters and four
slots. It is not an `assembleFill` reconstruction, and a general `CycleMin`
run list need not equal the run list of a fill. Exact interval counts are
unknown, not zero. There is no `no_cycleMin_four_even` and no
`no_cycleMin_necklace` here; the necklace slack argument is `REFUTED` and the
pin misses above are why. Occupation of both 2+2 seam windows by realized
cycle minima is `COMPUTATIONALLY VERIFIED`, not Lean.

Collision factorization at an arbitrary vertex lives in
[CyclePosition.lean](../../formal/Problems/Juggler/CyclePosition.lean) and the
valley fork in [Seam.lean](../../formal/Problems/Juggler/Seam.lean); neither
is re-derived here.

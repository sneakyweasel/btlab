# Orphan declaration gate

## Problem

Whether the 439 declarations the Lean hygiene gate reports as unreferenced are
dead mathematics, uncredited citations, or an artefact of the measurement.

## Exact statement

Let `D` be the public qualified declarations of `Problems.Juggler` and its
submodules, as read from the Lean sources by `trust_boundary.declaration_index`.
Let `R(d)` hold when some scanned source file contains an identifier token that
resolves unambiguously to `d`, excluding the declaration header of `d` and
recursive self-reference. The gate counts the `d` in `D` with `R(d)` false and
asserts that count is at most `ORPHAN_RATIO_NUM / ORPHAN_RATIO_DEN` of the live
candidate inventory. It was an absolute `ORPHAN_BUDGET` until 18 September 2026;
see Results.

The question is not the value of that count. It is whether the failure of
`R(d)` implies that `d` is unused, for which the relevant relation is the
compiled one: does any other constant in the elaborated environment mention `d`
in its type or its value?

## Current literature

`independent`. No external result is involved; this is a laboratory
instrumentation question. The prior art inside the repository is commit
44f3aa02 of 2026-09-08, which triaged the same clusters under the previous
metric, found that the clusters are not dead mathematics, and deleted nothing.
That finding is reproduced here and extended with compiled evidence.

## Branch budget

- **Target:** does the lexical orphan set coincide with the compiled dead set?
- **Novelty hypothesis:** none mathematically. The hypothesis under test is
  instrumental: that a cheap lexical proxy had been standing in for an
  expensive compiled relation and was being read as the real thing.
- **Falsifier:** the two sets agree, which would make the backlog genuine dead
  code and retirement the right answer.
- **Already killed by?:** no. 44f3aa02 reached a compatible conclusion on the
  previous metric, but without a compiled dependency graph.
- **Existing machinery:** [lean_hygiene.py](../../tools/lean_hygiene.py),
  [trust_boundary.py](../../tools/trust_boundary.py), and the compiled build
  artefacts already present in the main checkout.
- **Maximum Phase-0 scope:** load the compiled environment once, take the
  reverse dependency edges into Juggler declarations, and compare.
- **Promotion criterion:** none available; instrumentation is not a branch that
  can promote.
- **Stop criterion:** the partition is established and the gate measures what
  its own docstring claims.

## Balanced-ternary formulation

None. The objects here are Lean constants and reference edges, not integers in
a radix representation.

## Why BT may be relevant

It is not. This branch is recorded because the ceremony requires every decision
to carry a dossier, not because balanced ternary bears on it.

## Candidate operations / invariants

The invariant sought was that `R(d)` agrees with `C(d)`, where `C(d)` holds
when some constant other than `d`, and not an auxiliary child of `d`, mentions
`d` in its type or value in the elaborated environment. `OBSERVATION`: the two
disagree in both directions.

## Experiments

Not a registered probe. The evidence is a one-shot environment walk, recorded
here rather than added as a runner, because it needs a full Lean build and
cannot run inside the test suite.

Method: the module search path was pointed at the main checkout's build tree,
whose Lean sources are byte-identical to this branch modulo line endings, and a
`CoreM` action imported `Problems.Juggler` and `Problems.JugglerPaper`, walked
the constant map, and emitted every edge into a Juggler-module constant from a
constant that is neither that constant nor one of its auxiliary children.
10346 Juggler constants were seen, against 4836 public source declarations.

Partition of the 439, all four parts counted:

| Part | Count | Evidence |
|------|-------|----------|
| Live, consumed in the compiled environment | 12 | reverse edges exist |
| Cited only by a theorem-ledger `decl` field | 20 | registry row |
| Live but reached only by an ambiguous token | 8 | reverse edges exist |
| No consumer and no citation | 384 | neither |

The 12 and the 20 are measurement defects and are repaired in
[lean_hygiene.py](../../tools/lean_hygiene.py). The 8 are the documented
limitation: `J.cutForbiddens`, where `JoinFigure` and `SureLetterSite` both
carry that field name, resolves to two declarations, and the scanner reports
the token in its ambiguous set rather than crediting both. After repair the
gate reports 404, of which 8 are known live and 396 are the reviewed backlog.

Two further facts bear on the decision:

- No module on disk is wholly orphaned. The worst ratio is 50 percent, and the
  largest clusters by module are `IdealCycleMin` at 48 of 159 and
  `IdealLollipop` at 44 of 86 — neither one a cubic-band or quartic-band layer.
  There is no dead layer to retire.
- The namespace grouping that suggested otherwise is not a module grouping.
  The 20 declarations under namespace `Problems.Juggler.CubicGrid` live in five
  different modules, and the `CubicGrid` module contributes one of them.

## Conjectures

None. No statement here is a conjecture about the Juggler map.

## Counterexamples

`SeamData.cycleParent` in [Seam.lean](../../formal/Problems/Juggler/Seam.lean)
is the counterexample to reading the gate as dead code: it has 11 consumers in
the compiled environment and is reported as an orphan, because every use is a
projection on a binder. `JoinFigure.rigidity` in
[IdealLollipop.lean](../../formal/Problems/Juggler/IdealLollipop.lean) has 8.
Deleting the lexical orphan set would have removed both.

## Formalization

No Lean module is added, removed, or edited by this branch. The 396 reviewed
declarations remain compiled and kernel-checked exactly as they were. No
`sorry`, `admit` or `axiom` is introduced anywhere.

The 18 September clearing keeps that property: it is documentation only. One
page is new,
[the ideal-cycle model](../architecture/juggler_ideal_cycle_model.md), and
three existing ones gained sections. `lake build` output is therefore
unchanged and the warning budget is untouched, which is also why this pass
carries no build evidence: there is nothing for the compiler to say about it.

## Results

`OBSERVATION` the docstring of the gate was accurate and was being read past.
It says the check is not a dead-code proof, and that type-directed and
open-namespace references need compiled evidence. Both caveats were load
bearing, to the tune of 20 live declarations.

`OBSERVATION` the cap was never calibrated against the metric it guards.
285 was set in 44f3aa02 against basename substring counts over a generated
index; 555775aa of 2026-09-11 replaced the metric with namespace-resolved
qualified identifiers and carried the cap across unchanged. The count at
555775aa was already 432, so the gate was red the day that implementation
landed. The sequence since is 432, then 437, then 439, across three days of
heavy Lean work. That is not a long drift.

`OBSERVATION` the theorem ledger does not count as a citation.
[render_theorem_ledger.py](../../tools/render_theorem_ledger.py) never emits
the `decl` field into the scanned markdown, and JSON is outside the scanned
suffixes, so 20 declarations registered in the laboratory's own declaration
registry were reported as cited by nobody.

`OBSERVATION` an absolute cap does not survive the corpus it guards.
The cap was calibrated at 402 against 4836 candidates. Paper B's formalisation
then added 257 declarations, 28 of which nobody had written a sentence about,
and the gate went red at 433. Read as a count that is a regression; read as a
share it is an improvement, because citing the 28 left 405 of 5093, or 7.95%,
against the calibrated 8.31%. The corpus grew by 5% and got proportionally
cleaner, and the gate called that a failure. A count cannot distinguish more
unreviewed backlog from more mathematics, and only the first is what this gate
exists to catch.

The bound is therefore a share as of 18 September 2026, held as two integers
and compared by cross-multiplication so no float enters the verdict. 796/10000
admits 405 of 5093 and refuses 406, so the ratchet is exactly as tight as the
count was on the day it was set. The discipline is unchanged and so is its
wording: lower it when a cluster clears, never raise it to go green.

What the change concedes, stated rather than discovered later: 500 further
*cited* declarations raise the absolute allowance from 405 to 445. That is the
intended behaviour -- a growing corpus is allowed a proportionally growing
review queue -- but it does mean the absolute number of uncited declarations
can rise without the gate objecting, provided the cited corpus rises faster.
A count would have caught that and did not survive long enough to.

### Second episode, same day: the clusters cleared

`OBSERVATION` the share went red again within hours, at 413 of 5168, and the
branch that surfaced it was not the cause. The bound was 796/10000 at the
time, which allowed 411 there, so the failure was by two. Removing the jump-spectrum module and re-running the
report gives 413 of 5138, a share of 8.04 percent against the 7.99 percent
the same corpus carries with it: the new module cites all thirty of its own
declarations and *lowers* the share. The red was repo-wide and predated the
branch, which is what a share is supposed to make visible and did.

`OBSERVATION` the remedy was citation, not deletion, and it cleared six whole
clusters rather than the two declarations the gate asked for. The two largest
clusters by module are the ones this dossier already named:
[the ideal-cycle model](../architecture/juggler_ideal_cycle_model.md) now
documents `IdealCycleMin` (48) and `IdealLollipop` (43), which had no dossier,
no ledger row and no account anywhere but their own module docstrings. The
[Lean interfaces note](../architecture/juggler_lean.md) gained the
`RankedReturn` Euclidean induction (11), the `RealizedGridBounds` (7) and
`FullUpperCellChargeBounds` (7) accessors, and Paper B Section 6's printed
constants in `DepthFourFive` (10). That is 126 declarations, 287 of 5168
remaining, a share of 5.55 percent. Nothing was deleted, no Lean source
changed, and the worst per-module ratio fell from 50 to 45 percent.

`OBSERVATION` the Paper A release pin reaches prose, and the Section 6
paragraph was written into the wrong file first. The formalization map is the
natural home for it and is one of three markdown inputs whose SHA-256 sits in
`paper_a_release.json`, so adding a sentence to it failed
`test_paper_release_gates` and would have cost a manuscript rebuild. It moved
to the interfaces note instead. This is the same coupling the warning budget
records for two Lean tactic cleanups, and it had not been written down on the
documentation side; it is now, in that note's maintenance section.

`OBSERVATION` the level was reset by the owner while that work was in
progress, and the two things are independent. 631e647c raises the numerator to
1000, with the reasoning recorded at the constant: an explicit reset after the
gate interrupted a third consecutive branch, taken as a decision about the
level rather than as a measurement, with nothing cited to reach it. The
headroom is the point of that decision. What the reset does not do is change
the backlog it refuses, and that is what the clearing above addresses; the two
are independent and both are recorded at the constant.

`OBSERVATION` the documented ambiguity limitation was understated, and
concentrated exactly where the review had least to go on. The earlier
partition put 8 declarations laboratory-wide in the "live but reached only by
an ambiguous token" part. Among the 126 just cleared alone, 16 were in that
position, twice the figure recorded for the whole corpus:
the seven display-contract projections shared by `SureLetterSite` and
`JoinFigure`, `RankedReturn.left`, `RankedReturn.right` and
`RankedReturn.terminal_actual_factorization`, the three
`FullUpperCellChargeBounds` cutoff methods, and the two `surplus_pos` and one
`gap_pos` shared across the charge and grid records. For those the scanner had
seen a use and refused to attribute it, which is the correct conservative
behaviour and is also why they sat in a backlog described as having no
consumer and no citation. Fifteen such remain among the 287.

`OBSERVATION` the partition's largest part was measuring the absence of
documentation, not the absence of consumers. 396 declarations were recorded as
having neither consumer nor citation, and the first 126 examined divided into
undocumented public interfaces and the supporting halves of results whose
headline was already cited -- not abandoned intermediates. The compiled
dependency review that produced that figure was accurate about the reference
graph; the inference from it to "backlog" was carrying the assumption that
somebody had already tried to write the documentation down.

## Open questions

Whether the 396 should eventually be pruned, and by what criterion. A
declaration with no compiled consumer and no citation is not thereby worthless:
it may be a terminal result whose only proper consumer is a reader. The missing
instrument is a way to distinguish a terminal theorem from an abandoned
intermediate lemma, which the reference graph alone cannot do. The docstring
coverage figure from 44f3aa02, 15 percent against 38 percent layer-wide,
remains the best available proxy and is still unaddressed.

The 18 September clearing narrows that question rather than answering it. 126
of the 396 turned out to be neither terminal theorems nor abandoned
intermediates but undocumented interfaces, a third category the partition had
no column for, and the instrument that separated them was a person reading the
module. The remaining 287 have not been triaged that way. What would decide
the rest cheaply is still open, and the honest position is that the reference
graph cannot do it: `SureLetterSite.isValley` and
`RealizedGridBounds.gap_pos` are indistinguishable from dead code in the
sources and are load bearing in the elaborated environment.

The level is not among the open questions, and saying so is part of the
record. 1000/10000 admits 516 against 5168 candidates and the figure is 287.
The distance is 103 from the owner's reset, which took the allowance from 411
to 516 against 413 orphans, and the 126 the clearing then removed from the
count. The first of those is a deliberate decision about how often this gate
should interrupt a branch, taken after it interrupted three in a row, and the
room it leaves is the point of it rather than an oversight to be reclaimed. So
the arithmetic is recorded here and nothing is proposed: the smallest
numerator that still admits 287 of 5168 is 556. Recompute against the
inventory of the day if that figure is ever wanted; it is the owner's to want.

## Decision

`PROMOTE`, superseding the `PARK` of the first pass on the same day. The
measurement is repaired, the cap matches the metric it guards with the
reasoning recorded at the constant in
[test_lean_hygiene.py](../../tests/tools/test_lean_hygiene.py), and the two
clusters that pass named as the largest are now documented rather than merely
counted. The gate reads 287 of 5168, a share of 5.55 percent, which would pass
at the 7.96 percent bound it was measured against as well as at the
10 percent the owner reset it to.

The declarations are still kept rather than retired, for the reason 44f3aa02
gave and this branch has now tested on 126 of them: no module is wholly dead,
so there is no layer to retire and no parked branch whose removal is implied,
and the first cluster examined closely turned out to be a display contract the
companion mirrors in TypeScript, where deleting a name silently breaks a
figure. Deleting proved lemmas scattered through eighty live modules would be
churn with a real downside, a full revalidation cost, and no reader benefit.

Best next question: the 287 that remain sit in modules whose *other* results
are cited, so the reader-facing question is no longer which declarations are
dead but which modules have a documented interface and which have only a
docstring. Is per-module documentation coverage the gate that would have
caught this, where a share of the whole corpus did not say where the backlog
was?

## Publication assessment

Status: `ARCHIVED`. Laboratory instrumentation with no mathematical content.

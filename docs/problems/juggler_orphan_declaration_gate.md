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
asserts the count is at most `ORPHAN_BUDGET`.

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

## Open questions

Whether the 396 should eventually be pruned, and by what criterion. A
declaration with no compiled consumer and no citation is not thereby worthless:
it may be a terminal result whose only proper consumer is a reader. The missing
instrument is a way to distinguish a terminal theorem from an abandoned
intermediate lemma, which the reference graph alone cannot do. The docstring
coverage figure from 44f3aa02, 15 percent against 38 percent layer-wide,
remains the best available proxy and is still unaddressed.

## Decision

`PARK`. The measurement is repaired and the cap now matches the metric it
guards, with the reasoning recorded at the constant in
[test_lean_hygiene.py](../../tests/tools/test_lean_hygiene.py). The 396
remaining are kept rather than retired: no module is wholly dead, so there is
no layer to retire and no parked branch whose removal is implied, and deleting
proved lemmas scattered through eighty live modules would be churn with a real
downside, a full revalidation cost, and no reader benefit. That is the same
conclusion 44f3aa02 reached on the same clusters, for the same reason. Best
next question: can a terminal theorem be distinguished from an abandoned
intermediate lemma without a human reading each one?

## Publication assessment

Status: `ARCHIVED`. Laboratory instrumentation with no mathematical content.

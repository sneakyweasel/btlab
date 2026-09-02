# Discovery methodology

How a mathematical direction is opened, bounded, and ended in this
laboratory. Claim labels live in [README.md](README.md); this page is
about process, not about evidence strength.

The laboratory does not try to maximise modules, milestones,
visualizations, or discovered fibre types. It tries to maximise new
mathematical understanding per unit of exploration. Accumulated code and
Lean proofs are valuable because they make the next question cheaper.

## The loop

```text
Explore → Distill → Prove / Refute → Decide
```

### Explore

Cheap experiments that decide whether an idea has structure. Brute
force, small exhaustive searches, visualizations, ad hoc scripts,
prototype CLI commands, temporary representations, counterexample
searches. Do not optimize or generalize here. The purpose is discovery.

### Distill

When a pattern appears, stop expanding the implementation and ask what
the smallest statement is that explains the observation: an invariant, a
recurrence, an equivalence relation, a valuation law, an image problem,
a structural decomposition, a counterexample, an obstruction. Prefer
mathematical compression over more code. Interesting examples become one
candidate theorem, conjecture, or refutation.

### Prove / Refute

Attack the candidate: symbolic derivation, exact arithmetic, exhaustive
finite search, valuation arguments, Lean, independent derivations. Every
result gets a claim label from [README.md](README.md). Computational
evidence is never silently promoted to a theorem. Counterexamples are
first-class outputs and are recorded permanently.

### Decide

Every branch ends in exactly one of `PROMOTE`, `PARK`, `CLOSE`. See the
decision vocabulary below.

## Branch budget

Write this block before substantial implementation:

```text
Mathematical target     one precise question
Novelty hypothesis      what could possibly be new
Falsifier               the observation that kills the idea
Existing machinery      what the platform already provides
Maximum Phase-0 scope   the smallest experiment that answers the target
Promotion criterion     what would justify PROMOTE
Stop criterion          what forces PARK or CLOSE
```

Default maximum exploratory depth: one triage phase, then at most one
follow-up theorem phase. Do not open an unbounded sequence of
milestones. Extend a branch only when a prior phase produced a result
that justifies continuation.

Implement only the minimum required to answer the triage question. Do
not silently expand the scope.

## Decision vocabulary

`PROMOTE` — there is a genuine new theorem, a strong structural result,
a useful invariant, a meaningful exact obstruction, or a promising new
application. Then formalize, add the ledger row, document, and build
supporting tools only as far as the result justifies.

`PARK` — the mathematics is interesting but incomplete and the expected
payoff is currently lower than another branch. Keep the statements,
code, experiments, counterexamples, and the dossier. Do not continue
automatically. Parked modules stay in the tree and are not a second
frontier.

`CLOSE` — the idea is a known result or a reparameterization, no
nontrivial new theorem appears, the natural invariant search is
exhausted, the remaining work is brute-force taxonomy, or a precise
obstruction shows the branch is not promising. A closed branch must be
documented well enough that the project does not rediscover it.

Laboratory `CLOSE` does not imply that the mathematical question is
settled. Engine campaigns additionally carry a **primary close tag**
and a **mathematical status** (`research_engine.control`):

- close tags: `CLOSE_KNOWN`, `CLOSE_REPARAMETERIZATION`,
  `CLOSE_FALSE_OBSTRUCTION`, `CLOSE_FINITE_CENSUS`,
  `CLOSE_SKIP_BOUNDARY`, `CLOSE_SPEC_MISMATCH`, `CLOSE_NO_PROMOTION`
  (exactly one);
- mathematical status: `RESOLVED`, `STRONG_NEGATIVE`, `FRONTIER`,
  `UNRESOLVED`.

`CLOSE_SKIP_BOUNDARY` with `FRONTIER` means the executable attack
vocabulary is exhausted and the question remains open.
`CLOSE_FALSE_OBSTRUCTION` with `STRONG_NEGATIVE` means the investigated
mechanism was falsified. Finite census, prefix, or budget evidence
must not be upgraded to `RESOLVED`. These fields live on campaign
control records; they do not replace `PROMOTE|PARK|CLOSE` on problem
dossiers.

Older entries in [research_journal.md](research_journal.md) and in the
theory pages said *Outcome A / B / C*. That vocabulary is retired.
Outcome C was `CLOSE`; Outcome B, a known core with a project-specific
layer, was `PARK`; Outcome A was `PROMOTE`.

A successful theorem does not imply another milestone. A failed
conjecture does not imply another rescue attempt. Before continuing a
branch, ask:

1. Is there a materially new mathematical question?
2. Is the expected payoff higher than an alternative branch?
3. Can the next step be validated or falsified inside a bounded phase?
4. Does existing machinery materially help?
5. Would failure produce useful negative knowledge?

If the answer is mostly no, `PARK` or `CLOSE`.

## Claim tags and the novelty axis

Claim labels (`EXACT — LEAN VERIFIED`, `EXACT — HUMAN PROOF`,
`COMPUTATIONALLY VERIFIED`, `CONJECTURE`, `OBSERVATION`, `REFUTED`,
`REPARAMETERIZATION`) measure how well a statement is established. They
are defined in [README.md](README.md) and are the only tags allowed in
[theory/theorem_ledger.json](theory/theorem_ledger.json).

Novelty is a separate axis, used as prose annotation in dossiers and
theory pages, never as a ledger tag:

- `KNOWN` — the statement is in the literature; cite a `literature/` id;
- `REPARAMETERIZATION` — a classical construction under a local name
  (this one is also a ledger tag, because it is a claim about the
  statement itself);
- `PROJECT-SPECIFIC` — the measurement or refinement this project adds;
- `OPEN` — no proof and no refutation yet.

A branch whose statements are all `KNOWN` or `REPARAMETERIZATION` is a
`CLOSE`, however much machinery it produced.

## Machinery policy

The repository is a research platform with interchangeable mathematical
branches. Reusable primitives — balanced digits, sections, residual
states, Newton coordinates, valuations, finite-horizon equivalence,
fibre analysis, lifting, Lean proofs, visualization — belong to the
platform. Machinery is not itself a research result.

Before adding a component, ask whether it supports more than one
plausible direction. Prefer reusable primitives over problem-specific
infrastructure, and a small experimental module over a large generic
framework. Do not build infrastructure to justify a weak direction.

### Machinery gravity

The failure mode to watch for:

```text
new pattern → new data structure → new CLI → new visualization
→ another edge case → another subsystem → no new mathematical consequence
```

When this is detected: stop implementing, name the mathematical
question, search for a unifying invariant or obstruction, then decide.
Do not keep generating finer taxonomies without a theorem-level payoff.

Layer the work accordingly. Mathematical triage decides whether the idea
is interesting; a theorem phase proves or refutes the core claim;
infrastructure — CLI, visualization, reusable library, Lean packaging,
benchmarking — comes only after the theorem survives. Tiny exploratory
visualizations are the exception, when they materially help find the
mathematics.

## Negative knowledge

Failures are kept, not discarded. The lookup is
[negative_knowledge.md](negative_knowledge.md). Search that page
before opening a branch. The underlying homes remain:

- `conjectures/refuted/*.json` — refuted registry entries;
- `REFUTED` rows in [theory/theorem_ledger.md](theory/theorem_ledger.md);
- the **Refuted ideas** line of each
  [research_journal.md](research_journal.md) entry;
- the **Counterexamples** section of each `problems/<id>.md` dossier;
- regression tests under `tests/regression/` and the named
  counterexample tests under `tests/unit/`.

Search these before opening a branch. Do not re-test a discarded
hypothesis unless new mathematics changes the situation.

Standing examples: sample minimization is not exact Myhill–Nerode
minimization; naive recursive reduction of \(x^3\) fails; \(Q\) admits
no bounded residue / valuation / \(B_t\) classifier; nonzero cross-depth
overlap is not exhausted by the zero spine; valuations do not determine
3-adic lifting behaviour.

## Branch dossier

Each branch has a portable dossier under `problems/<id>.md`, copied from
[problems/TEMPLATE.md](problems/TEMPLATE.md). It records the problem,
the known mathematics, the novelty hypothesis, the open question, the
exploratory evidence, theorems, refutations, computational range,
formalization status, the branch budget, and the decision. The dossier
is what lets the machinery be reused without inheriting unjustified
assumptions.

## Milestone report format

At the end of a phase, report exactly:

```text
What was learned      3–7 concise points
Strongest theorem     one statement
Strongest refutation  one false hypothesis or counterexample, if any
Reusable machinery    what enters the platform
Branch status         PROMOTE | PARK | CLOSE
Why                   one short paragraph
Best next question    exactly one
```

Then stop. Do not start the next milestone automatically, and do not
open a numbered milestone by default — a journal entry may be a
consolidation.

## Discovery versus presentation

During discovery: temporary abstractions, messy experiments, dead ends,
and aggressive counterexample search are all allowed.

In the mathematical record: drop obsolete experiments, separate `KNOWN`
from `PROJECT-SPECIFIC`, present the smallest successful abstraction,
keep negative results only where they explain the structure, and never
present the exploratory path as if it were the theorem.

# Prospecting the Juggler program: candidate objects ranked by estimated leverage

Status: laboratory prospecting note. Date: 6 September 2026.

Every ranking below is an **OBSERVATION** about the corpus as it stands
on this date. Nothing here is a theorem. This note is not a halt
theorem, not a "no cycle of any length" claim, not a termination
theorem, not a divergent-orbit existence claim, not a floor raise, not
a second manuscript, and not a Paper A, Paper B or Paper C edit. It
opens no branch and takes no decision beyond the one recorded at the
end. Every fact it quotes keeps the label and the ledger identifier it
already carries; nothing is re-tagged or upgraded here.

The question this note answers is narrow. Among the objects the
program currently makes visible — open hypotheses, stated-but-unproved
lemmas, missing invariants, and gaps between a human proof and its Lean
counterpart — which ones have a downstream consequence that is large
relative to the cost of establishing them? The estimate is a
prioritisation aid for choosing the next branch, not evidence about the
Juggler map.

Sources read for the ranking: [Paper A](juggler_finite_dynamics_note.md),
[Paper B](juggler_parity_discrepancy_note.md) and its
[audit ledger](paper_b_audit_ledger.md),
[Paper C](juggler_fate_almost_all_note.md),
the [OEOEE production dossier](juggler_oeoee_production.md),
the [Tao-reduction note](juggler_tao_reduction_note.md),
the [theorem ledger](theorem_ledger.md),
the [branch ledger](../juggler_branch_ledger.md),
[negative knowledge](../negative_knowledge.md),
the active conjecture records, and the Juggler Lean layer.

## The bar

A candidate is admitted only if all four hold.

1. It is visible in the corpus: an exact statement can be quoted from a
   file, a ledger row, or a conjecture record.
2. It is open in the sense that matters for it. An unproved statement
   must not be proved, refuted, or closed; a Lean-gap candidate must be
   a claim whose ledger row carries a human proof and an empty Lean
   column.
3. It is not fenced. Rows recorded in [negative knowledge](../negative_knowledge.md),
   refuted conjecture records, `CLOSE` dossiers, and the standing
   prohibitions of the laboratory map are excluded, and so are nearby
   reformulations of them.
4. Its claimed consequence is documented. If no file records what
   depends on the candidate, the dependency is not counted.

Twelve of the fifty-four objects examined failed one of these tests and
are listed in the last section rather than ranked.

## 0. The estimate — **OBSERVATION**

Each admitted candidate \(p\) carries a score vector

  \(S(p) = (\text{novelty}, \text{generality}, \text{proofability},
  \text{compression}, \text{computational gain}, \text{downstream
  reach})\)

with each coordinate in \(0\ldots 5\), together with a cost in the same
range. From these the note forms a discovery factor and an impact
factor,

  \(D(p) = (\text{novelty} + \text{proofability})/10\),

  \(F(p) = (\text{downstream reach} + \text{compression} +
  \text{computational gain} + \text{generality})/4\),

and ranks by the ratio

  \(R(p) = D(p)\,F(p)/\max(\text{cost}, 1/2)\).

The shape of the ratio is the point, not the arithmetic. A statement
that is hard and consequential can outrank one that is easy and inert;
a statement with no documented dependents cannot rank highly however
difficult it is. The abstract form of this ordering — a priority ratio,
its division-free comparison, and the fact that mining in decreasing
ratio order minimises the value-weighted waiting cost of a schedule —
is formalised in
[InformationField.lean](../../formal/Problems/Engine/InformationField.lean)
as `Prospect.priority`, `Prospect.Before` and
`waitingCost_insertionSort_le`. That file is generic mathematics about
ordering candidates; it says nothing about the Juggler map, and it does
not make the score vectors below anything other than estimates.

The coordinates are judgements, made by reading the corpus, not
measurements. Two independent passes over the same object differed by
one unit on several coordinates, which is why the ranking below is
reported in bands and why the top three are recorded as a tie.

## 1. Candidates

### 1.1 The coefficient rule and the \(E < 2\) linearisation criterion

Paper B section 7 screens contractor words by a per-letter rule: for
letters \(s < t\) the coefficient of the phase variable of letter \(s\)
inside letter \(t\) is a product of the intermediate exponents, and
linearisation is safe when the expansion factor stays below \(2\) at
the expanded defect. The rule is used to classify all \(127\)
contractors at depth seven, and Paper B itself calls the screen
negative evidence only. It is carried as prose tables and as pinned
Python in `paper_b_prefix_count`
([source](../../src/research/juggler_sequence/paper_b_prefix_count.py));
there is no ledger row and no Lean counterpart.

What a numbered lemma would change: the depth-seven classification, the
\(227/256\) ceiling, and the depth-ten to depth-thirteen screen would
rest on a stated identity rather than on a formula checked against five
paper constants and one orbit agreement. It would close a hole the
[audit ledger](paper_b_audit_ledger.md) records. It moves no density
exponent: the level-1 kernel it points at is parked twice.

The scope must be split when this is written. The chain rule for the
coefficient and the \(E < 2\) criterion are mathematics; the drift and
stop thresholds are hypotheses relative to Paper B's toolkit, and a row
that conflates them would be a definition wearing a theorem's label.

### 1.2 The never-contracting word count in Lean

The count of binary words of length \(d\) all of whose prefixes fail to
contract is a dynamic program over a triangle of integers, and the
counting inequality that turns an equidistribution hypothesis into a
density statement is `J-equidistribution-implies-density-one`, tagged
**EXACT — HUMAN PROOF** with an empty Lean column, as are its siblings
`J-rate-free-density-one`, `J-five-step-descent-density` and
`J-tao-loglog-depth-bound`. The Lean layer already carries the
predicates in
[ItineraryStats.lean](../../formal/Problems/Juggler/ItineraryStats.lean);
what is missing is the enumeration and the class count.

This is transcription with a high chance of success and a
correspondingly modest reward: the wall in these statements lives
entirely in the equidistribution hypothesis, and formalising the
unconditional half moves no status. It ranks where it does because its
cost is small, which is exactly the behaviour the ratio is meant to
have.

### 1.3 The last two compiler-trust holdouts

Two scans in the Juggler Lean layer are discharged by `native_decide`
rather than by the kernel:
[OstrowskiSandwich.lean](../../formal/Problems/Juggler/OstrowskiSandwich.lean)
and
[OstrowskiNumeration.lean](../../formal/Problems/Juggler/OstrowskiNumeration.lean).
The ledger records the layer as \(305\) kernel decisions, \(20\)
`norm_num`, and these \(2\). The route that was priced and rejected was
kernel reduction of the scans as they stand; a structural proof that
the two division chains agree is a different route and has not been
tried.

The consequence is bounded and clean: half a million decided instances
leave the trust boundary and the review barrel stops carrying a
compiler-trust assumption. No theorem, kill, or period bound changes,
because the results downstream already use the structural digit-sum cap
rather than the scanned one. The obstruction is process, not
mathematics — retiring the holdouts requires a manuscript sentence to
change, which a Phase-0 branch may not do.

### 1.4 The elementary production family

The [OEOEE dossier](juggler_oeoee_production.md) is labelled
"reduction complete, constants pending". Its section 11 writes the
constants for the first member end to end with measured slack, and its
own status paragraph says the author would not move the printed
exponent on a single pass, and that the right next step is an audit in
the style of the Paper B ledger, after which the promotion is
bookkeeping. Paper C carries the family in reserve.

Two things make this the most interesting entry in the list. First,
the consequence is a constant at the root of a table: the contagion
exponent feeds the reduction threshold and a chain of downstream
constants, so a successful audit recomputes many printed numbers at
once. Second, the corpus disagrees with itself about the status of the
route — the laboratory map records the relevant gap as a dynamical
averaging problem that is not opened, while the dossier says the gap is
closed exactly for the first member and open-ended only for the tail.
Both statements can be true of different objects, and the note flags
the reconciliation rather than resolving it.

Honest limits: the audit is of somebody's single pass, the toolkit
steps and the assembly are the dossier author's own, and the deep
census that would corroborate the tail is a computation the map
forbids. Only the first member is a bounded audit.

### 1.5 The recursion lemma at the root of Paper C

The abstract recursion lemma, its seed, and the tree-counting argument
of the reduction theorem are **EXACT — HUMAN PROOF** with an empty Lean
column (`J-tao-rate-implies-conjecture`), and
[FateContagion.lean](../../formal/Problems/Juggler/FateContagion.lean)
states in its own header that the analytic counting is not formalised
there. Formalising them would let every exponent in the ladder feed one
machine-checked lemma instead of being re-argued per production. It
would not make the conditional spine Lean-verified: the recursion is
fed by analytic fibre estimates that stay prose.

## 2. Ranking — **OBSERVATION**

| Rank | Candidate | \(D\) | \(F\) | cost | \(R\) |
|---|---|---|---|---|---|
| 1= | Coefficient rule and \(E < 2\) criterion as a numbered lemma | 0.60 | 1.75 | 1 | 1.05 |
| 1= | Never-contracting word count and the counting inequality in Lean | 0.60 | 1.75 | 1 | 1.05 |
| 1= | Retirement of the two compiler-trust holdouts | 0.50 | 2.00 | 1 | 1.00 |
| 4 | Audit of the first production member's constants | 0.50 | 2.00 | 2 | 0.50 |
| 5 | Recursion lemma and tree count in Lean | 0.50 | 1.75 | 2 | 0.44 |

The three leaders differ by less than the granularity of the score
vector; the order among them is a tie-break, not a measurement. The
band is what the estimate supports: three cheap closures of comparable
value, then a costlier audit whose payoff is larger but whose inputs
are one person's single pass.

A pattern in the table is worth recording, because it is the honest
conclusion of the exercise. Every surviving candidate sits below the
frontier of the program. None of them touches the free-term hypothesis
of Paper C, the derandomisation wall of Paper B, the classical analytic
bricks under Paper A, or the equidistribution hypothesis that all three
density statements rest on. The high-reach objects in the corpus are
precisely the ones with near-zero estimated proofability, and the ratio
demotes them for that reason. Ranking by leverage finds cheap
consolidation, not a way past a wall; it says where the remaining proof
complexity is compressible, not where the problem is.

## 3. What the ranking does not decide

No candidate is promoted here. Opening any of them requires the triage
block the [methodology](../methodology.md) prescribes — target, novelty
hypothesis, falsifier, existing machinery, maximum scope, promotion and
stop criteria — and a decision of `PROMOTE`, `PARK` or `CLOSE` recorded
in the [branch ledger](../juggler_branch_ledger.md).

Three entries carry a process constraint that must be settled before
any work: the holdout retirement, the run-suffix headline, and the
margin-law rewrite each imply a manuscript edit, which a Phase-0 branch
may not make. They are consolidation-turn work.

Twelve examined objects were excluded rather than ranked. Three were
already established and the ranking pass had mistaken their status: the
closed form for the triple constant, the fan balance law, and the
per-thread contagion corollary are all recorded as proved, the last
with the ledger row `J-clotho-threads-per-thread-contagion`. The
remaining exclusions are fenced rows — the derandomisation obstruction,
the refuted localisation `J-kernel-localize`, the walk-competition
cluster recorded as terminal, and the flight programme recorded as
descriptively terminal. Those fences stand; this note does not reopen
them, and the ranking above must not be read as an argument for
revisiting anything on that list.

The region judgements behind the ranking are similarly provisional. The
tail of the [journal](../research_journal.md), the production dossier,
the hypothesis hierarchy of Paper C, and the section-7 screen of Paper
B are where open objects are concentrated; the settled expositions and
the closed branches are not. That is a statement about where to look,
made on this date, and it will be wrong as soon as the corpus moves.

## 4. What is and is not claimed

- The score vectors, the ratio, the ranking, and the region judgements
  are **OBSERVATION**: estimates about the corpus on 6 September 2026,
  not properties of the Juggler map.
- Every quoted statement keeps its own label and identifier. The
  contagion exponents, the reduction threshold, and the certified floor
  are quoted at the values the papers print; none is changed here.
- Nothing unconditional is claimed. No fate is excluded, no orbit is
  shown to terminate beyond the certified floor, no floor is raised,
  and no conjecture is settled.
- This is not a halt theorem, not a termination theorem, not a "no
  cycle of any length" claim, and not a second manuscript.
- The Lean ordering results this note refers to are about abstract
  candidate schedules. They are not about the Juggler map and they
  confer no status on any candidate ranked above.

## Endpoint

Branch status: no branch is opened by this note; the fences it touches
stay as they are.

Best next question: does an audit of the first production member's
constants, in the style of the Paper B ledger, survive — and if it
does, which printed constants in Paper C change, and does the
laboratory map's fence on that gap still describe the same object the
dossier closed?

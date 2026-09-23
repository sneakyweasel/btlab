# Recent research decisions

The latest twelve entries are kept here for orientation. Durable statements,
proofs and decisions belong in the [claim ledger](theory/theorem_ledger.md),
branch dossiers and proof maps. Search those records before relying on an older
journal claim; later proofs can supersede earlier open boundaries.

The earlier full-length journal is available at Git revision
`6512810cf65a4dd092a962a9c535e45b5f74614f`; see [recovery instructions](history.md).
New entries should name the changed result, its evidence, remaining premise,
decision, and canonical record. Keep the journal brief.

## 2026-09-23 -- Beatty phase profile as a positive jump series

The qualitative logarithmic-slope theorem is now **EXACT — LEAN VERIFIED**:
`r c_r/binom(m_r-1,r-1)-F(delta_r) -> 0`, with
`F(delta)=1+sum_{delta_r<delta} c_r beta^r (1-beta)^(m_r-r)`.
The finer binomial phase limit discharges the survivor asymptotic input;
finite first moments prove critical first-passage mass one; exact reindexing
identifies the whole jump series, with total mass `1/(alpha-1)` and first
jump `beta`. The complete accumulation set is now also Lean-checked: the
envelope minus the explicit open jumps is compact, perfect and Lebesgue-null.
Every gap endpoint is a subsequential limit, and closed intervals strictly
inside gaps are eventually avoided. The empirical law is now proved to be
`F_*(uniform[0,1])`, atomless and singular with respect to Lebesgue measure,
with continuous CDF `G`, exact identity `G(F(t))=t` and plateau height `delta_j`
on the j-th closed jump interval. The gap weights now have checked sharp
order `r^(-3/2)`; the exact tube formula gives `lambda(K_epsilon)` of order
`epsilon^(1/3)` and Minkowski dimension `2/3`. Ten consumer dependency
records check the original-count interfaces. Hausdorff dimension and an
exact tube leading constant remain open. Quantitative phase rates, effective numerical
constants and arbitrary irrational slope remain separate extensions.
**PROMOTE** the completed qualitative
specialization; no paper/release, priority or trajectory-termination claim is
changed. Canonical proof boundary: Sections 13–16 of the
[comparison note](theory/juggler_beatty_first_passage_note.md) and the
[dossier](problems/juggler_winkler_phase_collapse.md).

## 2026-09-23 -- OEIS generator corrections and exact modified-map descent

The bounded A325904 check found an empty-sum error at order two in the
printed A100982 transform, plus six stored generator terms inconsistent
with their recurrence. Exact coefficients and the repaired upper limit
reproduce 256 certificate counts and survivor depths 0..406.
**CLOSE** as a new counting method; the all-orders repaired identity
remains unproved here. See the [audit](problems/juggler_oeis_generator_check.md).

For A095396, a written floor-equality proof gives exactly one unit of
descent at every actual OE pair; actual EO pairs also strictly descend.
**PROMOTE** the bounded structural identity, with regressions through
10000 and at large perfect powers. No Lean or novelty claim, no termination
result, and no manuscript change. See [modified-map descent](problems/juggler_modified_juggler_descent.md).

## 2026-09-23 -- Cross-sign pairing has an actual two-generation deficit

Pairing the signed inverse coefficients gives a one-step lower bound 9/7,
but keeping each sign fixed for two steps gives joint coefficient
20064/29127 < 1 on the class 4 modulo 27. Lean checks both identities,
the exact complete sums, the affine bound and now the complete actual
reciprocal sums. Inverse-exponent pairs enumerate ordinary ancestors
without duplication, and the normalized paired mass on a=31+54t is below
3/4. Real summability is checked; signed positivity and oddness are shared.
**CLOSE** automatic compensation: iterating the one-step gain counts
mixed-sign paths; Juggler's two signed codes are negatives of one another,
not independent filters. The 3/8 pressure target is unchanged. See the
[dossier](problems/collatz_fibre_sign_coupling.md).

## 2026-09-23 -- Ancestor generating functions retain the harmonic-mass problem

The generating-function audit finds no lower estimate in the published
Hardy fixed-point or natural-boundary results. A nonperiodic root has a
single-source equation, not a fixed-point equation; harmonic mass uses
the Bergman norm, where expansiveness fails. Lean checks the ancestor
indicator's source equation, minimality, and the exact finite-energy
equivalence for arbitrary nonnegative weights. The known ancestor ray of
3 has finite harmonic mass and a natural boundary for both signs.
**CLOSE** this automatic analytic transfer; the unit-root word-count
target and Juggler pressure remain open. See the
[dossier](problems/collatz_ancestor_generating_audit.md).

## 2026-09-23 -- Every fixed repeated inverse block has summable mass off cycles

Lean extends the one-halving tail to any fixed positive inverse block w:
after one free exponent, D repetitions contribute at most
6*D_w(a)/2^(D*sum(w)) at a nonperiodic root, for either sign. The complete
first-exponent sum and total over all D are bounded. A zero affine anchor
forces a periodic root; the negative 5,7 cycle supplies a growing exception.
**PROMOTE** this family reduction. Finite unions of pure repeated-block
families cannot supply divergence; arbitrary switching remains unbounded.
The next signed-word target is a depth-averaged lower count for varying
actual words at a fixed integer. Juggler pressure and termination remain
open. See the [dossier](problems/collatz_fibre_word_tail.md).

## 2026-09-23 -- Near-critical periodic weights already require the global cell rate

Lean now transports any nonzero subsolution coordinate to a global
geometric lower bound at the same rate, with cost 3/2^(2*3^r) and one
depth shift. Therefore nonzero periodic tables at rates tending to one
already imply uniform subexponential cell lower decay. **CLOSE** treating
the capped family as an easier local shortcut; its root-prefactor bound
is additional. This downgrades the proposed 1-1/r scale, without refuting
it. The next target is a direct actual-word lower count at one ordinary
integer. No coefficient divergence or Juggler input follows. See the
[dossier](problems/collatz_fibre_rate_barrier.md).

## 2026-09-23 -- Capped weights improve fixed-root constants; the near-critical bound remains open

Lean constructs the greatest bounded periodic subsolution at each rate and
level, with monotonicity under ternary refinement at a fixed rate. Exact
lower/upper iteration brackets all coordinates within 10^(-9) at levels
1–4. At level four and q=3/4, the root-to-deficit ratios improve from
0.281 to 0.466 for plus root 7 and from 0.146 to 0.256 for minus root 47.
**PARK** further finite tables. The remaining target is a positive lower
bound on that ratio along rates tending to one; no coefficient divergence,
Juggler pressure or termination follows. See the
[dossier](problems/collatz_fibre_subsolutions.md).

## 2026-09-23 -- Fixed-root coefficients are at most linear; block-minimum weights lose their prefactor

Lean now bounds both signed complete unit coefficients by A_s(a)*(d+1)
at each nonperiodic positive odd root, using actual endpoints, harmonic
mass and the finite-height tail. The all-source bound loses only 21/5.
For geometric generation blocks whose rate is certified by the block
minimum, the normalized root weight divided by 1-q is at most
4*A_s(a)*N^3*(2/3)^(N-1), and tends to zero. **CLOSE** that construction;
other periodic subsolutions and fixed-root divergence remain open. Fifteen
exact controls pass. No Juggler pressure or termination follows. See the
[dossier](problems/collatz_fibre_block_weights.md).

## 2026-09-23 -- Subcritical weights isolate the missing fixed-root constant

Lean checks that L_s h>=q*h with 0<=h<=1 gives C_d(a)>=q^d*h(a),
and that a family q_i tending to one forces divergence if its normalized
root values stay above c*(1-q_i). Both family premises remain open.
Eight exact Python certificates at levels 1–4 reach q=0.771500620;
they establish no asymptotic rate or root constant. **PARK** further finite
tables; the next target is the analytic family estimate. The newly located
Nikpour–Rabbani preprint is registered as an unchecked abstract claim,
not a verified input. No Juggler pressure or termination follows. See the
[dossier](problems/collatz_fibre_critical_minorants.md).

## 2026-09-23 -- One fixed ternary class already transports lower bounds globally

The previous recommendation supplied no new fixed-root lower count. The
proposed neighborhood shortcut now has an exact limitation: every positive
odd unit root has an actual predecessor in any class modulo 3^r, with
exponent at most 2*3^r. Lean checks simultaneous coefficient transport and
finite-block bounds at cost 3/2^(2*3^r), plus equivalence of class-wide and
global divergence at nonperiodic unit roots. **CLOSE** this route as a weaker
uniform arithmetic target. Six exact controls pass. No lower-count premise,
Juggler pressure or termination is proved. See the
[dossier](problems/collatz_fibre_lower_transfer.md).

## 2026-09-23 -- One-halving runs have summable fixed-root weight

At a fixed positive root a, all actual words with one arbitrary first
exponent followed by d one-halving steps contribute at most 3a/2^(d+1),
with total allowance 3a. Lean checks both signs, actual returns and the
necessary divisor; the negative fixed point a=1 is retained as a growing
exception. **PROMOTE** this summable-family reduction. Five exact controls
pass. Transported peaks cannot themselves supply fixed-root divergence;
the remaining word count and Juggler pressure stay open. See the
[dossier](problems/collatz_fibre_run_tail.md).

## 2026-09-23 -- Actual coefficient peaks defeat local Harnack comparison

A fixed exponent branch transports the actual one-halving spike into every
ternary unit neighborhood, for both signs. Lean proves coefficient values
above every bound at arbitrarily large depths and positive odd heights;
four independent actual-word and mean controls pass. **CLOSE** uniform local
Harnack comparison as a route from averages to a fixed-root lower bound.
The peak's integer target varies with depth, so fixed-integer divergence and
Juggler termination remain open. See the
[dossier](problems/collatz_fibre_local_bounds.md).

## 2026-09-23 -- Complete halving averages control the final unit loss

The actual signed operator retains between 5/21 and 20/21 of its all-source
coefficient when sterile sources are removed, at every positive depth. The
factor is paid once. **PROMOTE** this relative comparison and its equivalence
with the finite-budget series; the fixed-root coarse lower bound remains open.
Lean checks the comparison and the conditional reciprocal-ancestor consequence.
Eight independent affine-distribution controls pass. No termination or Juggler
transfer is claimed. See the [dossier](problems/collatz_fibre_unit_comparison.md).

## 2026-09-23 -- Conditioned Syracuse decay reaches the modulus but not fixed-root precision

The new reading audit checks Si's 2026 conditioned affine preprint against the
actual signed finite-height quantity. A total-exponent slice selects exactly
two cells modulo 3^(d+1); four independent composition controls agree with
actual inverse paths and budget increments. Theorem 5.1 reaches that modulus,
but absolute-value Fourier inversion leaves an error multiplied by 3^d and
supplies no relative lower bound. **CLOSE** this direct transfer. The signed
frequency sum and the actual fixed-root count remain open. No new Lean theorem
or analytic lower bound is claimed. The Kramer record's title and arXiv URL
are also corrected. See the [reading audit](problems/collatz_conditioned_syracuse.md).

## 2026-09-23 -- Mixing alone does not force fixed-integer coefficient divergence

The fixed-root recommendation produced no arithmetic lower bound. An explicit
coherent ternary density now shows why positivity and even uniform exponential
refinement control cannot supply one: at any selected ordinary unit integer,
its density series sums to 3/2. A second normalization matches the initial
Syracuse row (0,1,2). Lean checks both models and a constraint separating the
unit model from the actual signed operator; seven rational controls pass.
**CLOSE** the inference from mixing alone. Exact signed recurrence, the
fixed-root lower bound and Juggler growing-depth pressure remain open. See the
[dossier](problems/collatz_fibre_mixing.md).

## 2026-09-23 -- Finite height budgets retain the full coefficient-divergence target

The preceding recommendation supplied no new lower bound. The next phase
removes a separate obstacle: at either signed Collatz map, restricting a
depth-d inverse family to total halving exponent at most 8d loses at most
(19683/32768)^d of its homogeneous coefficient. Lean checks the complete
error, actual ancestor support below a*256^d, summability equivalence, total
error allowance, and conditional actual reciprocal divergence. Seven exact
controls include independent forward source enumeration. **PROMOTE** this
cutoff reduction; the fixed-root depth-block lower bound and Juggler pressure
remain open. See the [dossier](problems/collatz_fibre_height_budget.md).

## 2026-09-23 -- Bounded branch-specific stopping still leaves poor fibres

The previous turn recommended coefficient-series divergence but proved no new
estimate. The proposed variable-depth repair now has a precise limitation:
for either sign, every common finite stopping budget has a unit residue where
even the attained optimal branch-specific policy fails to reproduce its
periodic terminal weight. Lean checks the envelope, arbitrary policy domination
and actual integer representatives. **CLOSE** this bounded-stopping repair.
The poor target may depend on depth; unbounded stopping and fixed-integer
coefficient divergence remain open. See the
[canonical dossier](problems/collatz_bounded_fibre_stopping.md) for proof and validation.

## 2026-09-23 -- Finite-path packing removes the negative affine depth loss

- **Previous-turn audit:** The polynomial generation proof was completed and
  committed in bc779ab7. The proposed dyadic coefficient lower bound was still
  a recommendation with an open arithmetic premise.
- **Result:** Signed shortcut parity has exact residue moment 3^k. Packing
  the first N-5m states of a nonrepeating finite path and bounding its last
  5m states separately gives a summable reciprocal shell bound, uniformly
  over finite path length. A preperiodic target is allowed; future equal-time
  injectivity is not assumed.
- **Actual bridge:** The negative accelerated map is explicitly related to
  shortcut iteration by its odd part and return clock. The source reciprocal
  sum is at most one absolute B. Hence the affine product is at least exp(-B),
  and actual generation mass is at least K_d^-(a)/(a*exp(B)).
- **Consequence:** The sufficient negative coefficient series is now unweighted,
  like the plus criterion. Its divergence and the fixed-root dyadic lower
  bound remain open. No Juggler pressure or termination implication is asserted.
- **Attribution:** Packing is known; the five-step constants follow M. Sharpe's
  MIT-licensed OrbitPacking.lean. The signed moment, finite terminal-window
  correction and application to the complete negative generation operator are
  proved locally. No literature priority is claimed.
- **Validation:** Both modules compile; exact signed parity, finite-path,
  preperiodic-merger and periodic controls pass. The final proof map records
  the full-build and public-declaration audit outcomes.
- **Decision:** PROMOTE the uniform affine bound and the complete unweighted
  generation-series criterion. Stop this bounded phase. Arithmetic coefficient
  divergence and the larger termination goal remain open.
- **Proof map:** [uniform generation mass](theory/collatz_uniform_generation_mass_lean_note.md).

## 2026-09-23 -- Negative Collatz affine loss is polynomial on nonperiodic paths

- **Continuation audit:** The previous recommendation supplied a recalibrated
  target but no arithmetic counting theorem. The actual all-odd Juggler count
  remains open: the existing Paper B transfer covers two predecessor weights,
  and its next nested phase remains unsupported. At C=16, the existing
  shorter-prefix argument needs logarithmic saving greater than 3.865396808754;
  the suggested power-four count would control only the all-odd contribution.
  This calibration is recorded without promoting it as a counting result.
- **New mathematical result:** For S(n)=(3n-1)/2^v2(3n-1), an actual path
  to a nonperiodic target has distinct odd source states at least five. Its
  exact affine product has sixth power at least 1/(d+1), by Bernoulli's
  inequality and a telescoping comparison on the sorted distinct states.
  The negative affine comparison therefore costs at most (d+1)^(1/6).
- **Complete bridge:** `FibreDistortion.kernel_eq_path_sum` identifies the
  existing complete residue coefficient with all actual integer paths.
  Actual generation mass is at least K_d^-(a)/(a*(d+1)^(1/6)); nonsummability
  of the corrected coefficient series implies nonsummability of the literal
  natural-number reciprocal series of actual unit ancestors. Every halving
  exponent is included, and extended nonnegative sums require no prior
  finiteness of actual mass. The periodic root 1 is a checked negative control.
- **Earlier work completed:** Registered the pending plus-map criterion and
  generic disjoint-generation theorem. The written fate-class root-existence
  argument is separated from the given-target formal statement. The two
  coefficient-series divergence premises remain open; the minus theorem
  does not preserve the plus theorem's absence of a depth loss.
- **Validation:** Active Lean build passes 9,011 jobs. Audits cover all 17
  public generic/plus theorems and all 24 public negative theorems, using only
  propext, Classical.choice and Quot.sound. Eight new exact regression checks
  pass. Style, ledger rendering, branch index and Paper E release checks pass.
  The combined selected run has 47 passes and three failures caused by two
  concurrently deleted older ledger targets: docs/literature_comparison.md
  and formal/Representation/Words.lean. The new mathematical checks,
  declaration resolution, generated records and documentation links pass.
  The isolated source tree passes all 49 selected mathematical, ledger,
  declaration and generated-artifact tests; all unchanged ledger rows and
  named source paths are checked against its own base revision.
  Unrelated staged edits and deletions are excluded from the scoped commit.
- **Coverage:** HUMAN PROOF labels with kernel trust are retained pending
  advisory statement coverage; no external request was sent. The
  [proof map](theory/collatz_negative_generation_mass_lean_note.md) states the
  exact hypotheses, complete counting correspondence and remaining premise.
- **Decision:** **PROMOTE** the polynomial negative affine bound and the
  complete signed conditional generation criteria. Stop this bounded phase.
  No coefficient-series divergence, Juggler pressure bound, termination,
  infinite escape or new cycle exclusion is asserted. The full goal stays active.

## 2026-09-22 -- Actual signed fibre mass and persistent deficient targets

- **Continuation audit:** The preceding review confirmed the 5/8 contagion
  and 3/8 pressure thresholds without adding a theorem. This phase finishes
  the pending actual-integer bridge; it does not reopen finite-weight searches.
- **Scope and falsifiers:** Both signs, every finite ternary table, the full
  positive odd predecessor fibre, and its one-generation affine error. A
  missing predecessor, duplicate counting, incorrect signed denominator or
  unsummable error would invalidate the transfer. Higher-depth actual errors
  and generation-series divergence are outside this phase.
- **Proof:** `FibreActual` proves the bijection between admissible exponents
  and actual positive odd predecessors, and identifies every coefficient
  branch with its integer child. `FibreMassError` proves convergence both
  on exponents and directly on actual predecessors, then sums the geometric
  affine errors to H/(m-1/2). `FibreDeficit` turns the existing deficient
  residue into an explicit odd progression with divergent reciprocal mass.
  For every globally finite reciprocal-mass deletion, an actual deficient
  positive odd unit remains. The final theorem exposes the actual predecessor
  sum rather than requiring a reader to infer its meaning from a helper name.
- **Research consequence:** A positive periodic weight cannot copy Juggler's
  uniform production step by deleting a globally finite-mass poor set. This
  concerns ambient targets, not their intersection with a prescribed fate
  class. The growing-depth Juggler pressure estimate remains open at 3/8.
- **Coverage:** The ledger separates the formal one-generation error and
  actual deletion obstruction from the higher-depth written result. Kernel
  trust is recorded; HUMAN PROOF labels remain pending advisory coverage.
  No external statement was transmitted. Every new public declaration has
  a mathematical docstring and the source style gate passes.
- **Validation:** Full Lean build: 9,093 jobs. The complete 54-theorem audit
  uses only propext, Classical.choice and Quot.sound. Ledger rendering and
  branch-index consistency pass. The transient Paper E pyproject mismatch
  cleared when the concurrent edit was removed; its release check now passes.
  The targeted run has 88 passes and one stale-catalogue failure after
  concurrent tooling changes. Refreshing the records resolves that test;
  it and the declaration-resolution and documentation-link checks pass
  on rerun. The scoped commit's five generated artifacts match its own
  generator, and unrelated ledger edits are excluded. Details are in the
  [proof map](theory/collatz_actual_fibre_mass_lean_note.md).
- **Decision:** **PROMOTE** the actual-mass formalization and stop this
  bounded phase. No termination, infinite escape or new cycle exclusion is
  claimed. The full research goal remains active.

## 2026-09-22 -- Self-contained effective OOE coverage packet

- **Scope:** One bounded correction to the same theorem and same six
  declarations. The main counting errors, cutoff, witness and orbit
  conclusions are unchanged. Auxiliary proof-method and denominator
  observations remain in the proof notes rather than the focused ledger row.
- **Repair:** Supplied the filtered-range count, explicit cutoff, Juggler
  map and full actual-orbit predicate in the declaration documentation.
  Four Lean definition-equality checks confirm that context. Every exported
  header and docstring fits without truncation; theorem types and proofs
  were preserved.
- **Advisory:** One corrected `jev-1.13.0` request returned coverage 0.57,
  claim-broader 0.40, declaration-narrower 0.30 and different-result 0.13.
  The original 0.22/0.89 warning and both complete packets are preserved in
  the [review history](../data/research/formalpedia/ooe_coverage_reviews.json).
- **Ruling:** `EXACT — LEAN VERIFIED`, kernel trust, after direct coverage
  comparison, the definition checks, and the refreshed 59-declaration
  paper audit. The separate 23-theorem audit and exact 177147-row check pass.
  Independent review remains pending. This bounded repair is complete;
  no further Jev request or new research direction is opened.

## 2026-09-22 -- Complete signed coefficient obstruction formalized

- **Continuation audit:** The preceding review verified the new 5/8
  contagion threshold but added no theorem. This phase consolidates the
  existing finite-weight transfer obstruction instead of reopening its
  rejected search. Actual growing-depth Juggler pressure stays open.
- **Scope:** Both signs, every ternary level r>=1, every positive unit
  table, and every fixed positive generation depth d. A failed concrete
  mean identity or failed repeated-branch inequality was the falsifier.
- **Proof:** `Problems.Collatz.FibreMass` defines the full infinite sum
  over halving exponents. The signed congruence and child uniqueness are
  proved from the doubling permutation. Geometric domination justifies
  finite-sum interchange. The operator sum and the lifted base-weight
  sum both equal 3^d times the original sum, while the k=1 path at -s
  contributes at least (3/2)^d times its original weight. A deficient unit
  row follows. The stronger result permits zero weights on other units,
  provided h(-s)>0 and h is nonnegative and zero on nonunits.
- **Coverage:** Split the coefficient theorem from the actual-integer
  error/progression corollary in the ledger. The latter, sibling coverage
  and the generation-series criterion remain written proofs. The kernel
  result retains the HUMAN PROOF label pending advisory coverage; no
  external statement was transmitted.
- **Validation:** Full Lean build passes 9,090 jobs. All 31 theorem
  dependency audits use only propext, Classical.choice and Quot.sound.
  The shared-worktree regression run has 90 passes and 17 failures traced
  to concurrent OOE/Paper E edits: three accidental orbit-notation links
  in the peer ledger row, and a newly added Paper E input absent from its
  release inventory. The fibre, ledger and formalpedia tests pass.
  The scoped commit independently checks its changed-document links and
  generated registry against its own source tree, preserving peer edits.
- **Decision:** **PROMOTE** the formal consolidation. Uniform finite
  ternary reweighting remains closed for both signs and any fixed grouping
  depth. This proves no new Juggler pressure estimate, termination result,
  escape trajectory or cycle exclusion. The broader goal stays active.

## 2026-09-22 -- Scoped effective OOE Jev coverage check

- **Authorization and scope:** Sent only `J-effective-ooe-modular-return`
  and its six covering declarations, following explicit user authorization.
  One fresh Jev request was made; no other theorem was transmitted.
- **Advisory:** `jev-1.13.0` returned coverage 0.22, claim-broader 0.89,
  declaration-narrower 0.32, and different-result 0.13 (1792 input tokens).
  These scores flag the packet; they do not measure proof correctness.
- **Local review:** The exported headers hide the explicit cutoff value,
  the counting definition and the actual-orbit predicate. The core count
  and witness statements match after unfolding those definitions; the
  ledger also describes proof inputs and a separately covered denominator
  observation. Details and the unchanged advisory are in the
  [coverage review](theory/juggler_ooe_effective_return_lean_note.md#jev-coverage-review).
- **Ruling:** Retain `EXACT — HUMAN PROOF` with kernel trust until the
  advisory presentation discrepancy is resolved. No mathematical statement,
  Lean proof, constant or PDF changed. Independent review remains open.

## 2026-09-22 -- Actual OOEE production and unconditional 5/8 contagion

- **Continuation audit:** The preceding review completed the count-tail
  test record but proved no new mathematical result. The scoped count-tail
  release and registry check now passes all 48 selected tests.
- **Target:** Discharge OOEEProductionBound with its actual physical
  source cutoff. A weight or cutoff loss consuming the margin below 1/9
  would falsify the argument. No longer-fibre or new cycle branch was opened.
- **Proof:** At count tolerance 1/10000 and analytic size m>=10^9,
  card(F_m)>=(1107/10000)*m^(7/9) and n<=m^(16/9)+3*m^(7/9)
  give reciprocal fibre mass at least 11/(100m). The summable count-poor
  tail bounds the cost of discarding deficient targets uniformly over A.
  For m<=floor(exp(9t/16-4)), every source satisfies
  n<=2*exp(t-64/9)<=exp(t). Exact fourth iterates make fibres disjoint;
  backward closure places all their sources in A. The established mass
  comparison gives one conserved-weight loss for every A and every t.
- **Consequence:** OOEEProductionBound is unconditional. Every
  backward-closed class with a positive member has reciprocal mass at
  least K*(log X)^(5/8) eventually. The existing Tao and scale-average
  reductions now retain only their actual rate hypotheses at e>3/8
  and r-eta>3/8. Neither rate is proved; termination remains open.
- **Validation:** The full Lean build passes 9,089 jobs and all 11 theorem
  dependency reports contain only propext, Classical.choice and Quot.sound.
  The broad run and corrected publication-gate rerun cover 275 passing
  selected tests and 15 skips, with no unresolved failures. Details are in the
  [proof map](theory/juggler_ooee_weighted_production_note.md). No new
  external advisory request was sent; the ledger keeps kernel trust
  and pending statement coverage. The size threshold is analytic and
  does not raise the computational verification floor.
- **Decision:** **PROMOTE** the completed weighted-production assembly.
  Stop this phase here; actual growing-depth stopped pressure is the
  next mathematical obstruction, not a consequence claimed by this proof.

## 2026-09-22 -- OOEE count-poor resonance inclusion and reciprocal tail

- **Scope:** Complete the retained fixed-count-deficit inclusion and
  reciprocal tail. Target-dependent cutoffs or a lost counting exponent
  would falsify the argument. The weighted ratio and physical cutoff are
  left for the next phase.
- **Proof:** Choose the Fourier cutoff, then the resonance width, then the
  target threshold in the proved normalized fibre estimate. Both frequency
  signs reduce to a positive natural denominator. Every fixed absolute
  count deviation eventually lies in the family
  abs(q*(9/8)*m^(2/9)-z)<=C*m^(-7/9), 1<=q<=H.
- **Counting:** A fixed q contributes at most
  (80C+10q)*u^(2/9) targets in (u,2u]. Monotone arc counting retains all
  closed boundaries and needs no small-width condition. The union over
  q<=H is at most H*(80C+10H)*u^(2/9). Dyadic summation gives reciprocal
  tail at most 3H*(80C+10H)*U^(-7/9).
- **Consequence:** For each eta>0 the actual count-poor targets have an
  eventual reciprocal tail D_eta*U^(-7/9). Both finite upper cutoffs and
  summability with the infinite-series bound are proved.
- **Validation:** Both modules compile. All 22 new theorems pass the
  dependency audit with only propext, Classical.choice and Quot.sound.
  Full build and repository gates are recorded in the
  [proof map](theory/juggler_ooee_count_poor_tail_note.md). No external
  advisory call was made; the two new rows retain kernel trust and
  pending statement coverage. Paper E's registry pin and source archive
  were refreshed without changing its manuscript, PDF, TeX or metadata.
- **Decision:** **PROMOTE** the count-poor tail. The next question is
  conversion to the actual conserved-weight production with physical
  cutoffs. OOEEProductionBound, the stronger unconditional Lean exponent
  and the actual growing-depth pressure estimate remain open. This phase
  stops after the count-poor tail.

## 2026-09-22 -- Exact OOEE target fibres and normalized parity

- **Scope:** Complete the retained joint-parity application on its exact
  target fibres. Rounding losses consuming the short-interval saving were
  the falsifier; no longer-fibre attack or new pressure hypothesis was opened.
- **Proof:** The double-ceiling inverse thresholds give the exact unguarded
  cell. Its odd candidates have count (8/9)m^(7/9) with error at most 3;
  filtering by the actual OOEE guard is exactly the fourth-iterate fibre.
  For m>=64 the candidate count and source interval meet every hypothesis
  of the proved joint-parity theorem.
- **Consequence:** Outside the explicit slow resonance windows, the exact
  fibre's normalized count differs from 1/8 by at most
  15/sqrt(H+1)+(A_H^3+6*A_H)*(2B*m^(-1/18)+4/C+
  18*pi*H*m^(-2/3)+2*m^(-7/9)). B and the target threshold are independent
  of C. This preserves the order H first, C second, then m large.
- **Validation:** Both modules compile, the complete 26-theorem dependency
  audit uses only the three standard Mathlib axioms, and the full Lean
  build passes 9,085 jobs. Repository checks and the concurrent-publication
  boundary are recorded in the [proof map](theory/juggler_ooee_fibre_parity_note.md).
  No external advisory service was contacted; the two ledger rows retain
  kernel trust with advisory coverage pending.
- **Decision:** **PROMOTE** the actual fibre count. Fixed-deficit resonance
  inclusion, reciprocal-tail counting, weighted conversion and physical
  cutoffs remain before OOEEProductionBound. The unconditional Lean
  exponent remains 100/203; growing-depth pressure and termination are open.
  This phase stops here.

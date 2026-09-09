# Cycle order below the cubic height

Status: **PARK**. Research attempt dated 9 September 2026.

**The no-cycle conjecture is not proved.** The result obtained is a
conditional restriction on the complete itinerary of a primitive cycle.
If its maximum is below the cube of its minimum, its ordered states
must rotate by a fixed rank increment. Consequently its length and odd
count are coprime and its word is exactly a ceiling mechanical word.
The parity obstruction needed to exclude even this class is unproved.
Cycles reaching or exceeding the cubic height are also unexcluded.

The authorized continuation adds four exact results: common period and
interlacing for all cycles at one threshold; a uniform sorted grid in
log-log coordinates; cycles under a one-unit successor allowance at
every scale; and an explicit 11-cycle showing that even exact
within-branch gap data lose an additive branch constant. None proves
the required wrong-parity intersection for the exact map.

## Problem

Let
\[
J(x)=\begin{cases}
\lfloor\sqrt{x^3}\rfloor,&x\text{ odd},\\
\lfloor\sqrt{x}\rfloor,&x\text{ even}.
\end{cases}
\]
Can global order on a finite invariant set provide a cycle obstruction
that does not depend on making the logarithmic surplus small?
The concrete test is the class of primitive cycles with minimum
\(m>1\), maximum \(M\), and \(M<m^3\).

Paper A's certified period lower bound remains \(780239\). This work
does not raise the descent floor or exclude any further period.

## Exact statement

**Canonical proof source:** [Paper A, Section 3.10](../theory/juggler_finite_dynamics_note.md).
Theorem 3.33 through Proposition 3.38 contain the statements and full proofs.
The six theorem-ledger identifiers now point there. This dossier retains
research context and data, without a second editable proof source.

For an actual primitive cycle with m>1 and M<m^3, sorted states rotate by
the even count; the period and odd count are coprime, and the minimum-based
word is ceiling mechanical. The comparison map S_b uses the three-halves
floor below b^2 and the square-root floor above, on [b,b^3). It has cycles
at every scale, sharing a period and interlacing at fixed b. The exact
log-log grid and the two altered-map obstructions are Propositions
3.36--3.38. Uniform wrong-parity intersection remains open.

## Current literature

**Extended within the repository; external priority not claimed.**
[Paper A](../theory/juggler_finite_dynamics_note.md) supplies the
existing cycle bounds. [Method ceilings](juggler_cycle_method_ceilings.md)
identifies the missing global information.
[The earlier Christoffel branch](juggler_cycle_christoffel.md) refutes
an unconditional reduction based on finance or admissible open words;
it explicitly leaves actual-cycle rigidity open. Proposition 1 uses
the additional height hypothesis and injectivity on a closed orbit.
It does not contradict that earlier refutation or identify the
Christoffel word with the greedy charge maximizer.

[The corrected run-alphabet dossier](juggler_cycle_run_alphabet.md)
withdraws an argument from \(R<27/8\). That assertion stays withdrawn.
The order proof here uses the different, explicit hypothesis
\(M<m^3\), exact floor inequalities, and no zero-drift assumption.
[Mechanical-window experiments](juggler_cycle_mechanical_window.md)
already showed finite prescribed-word fixed points with failed parity
checks. Proposition 2 gives a finite invariant-set construction at
every scale, without enumerating a prescribed word's fixed-point band.

The map and the general convergence conjecture are documented in
[OEIS A094683](https://oeis.org/A094683) and
[Weisstein's Juggler Sequence entry](https://mathworld.wolfram.com/JugglerSequence.html)
(accessed 9 September 2026). No external analytic theorem is used in
the proofs below, and the finite searches do not establish novelty.

## Branch budget

- **Target:** exclude primitive cycles with \(M<m^3\).
- **Novelty hypothesis:** sorted-state order plus bijectivity forces
  a complete word, rather than another bound on the surplus.
- **Falsifier:** the forced word and exact integer closure still do
  not yield a contradiction to the actual parity requirement.
- **Already killed by?:** unconditional Christoffel and local-cell
  shortcuts are closed. The additional global height hypothesis and
  permutation argument are not supplied by those shortcuts; this is
  a restriction on complete words uniform over this height class.
- **Existing machinery:** minimum/maximum parity, exact square/cube
  cells, monotonicity of the two prescribed branches, primitive-cycle
  injectivity, and the recorded method ceilings.
- **Maximum Phase-0 scope:** written order proof; exact complete
  threshold graphs for \(3\le b\le30\); one start per threshold for
  \(3\le b\le10000\); four capped large-scale controls; explicit
  counterexamples to stronger interpretations. No floor campaign.
- **Promotion criterion:** a proved uniform parity obstruction.
- **Stop criterion:** retain the structural result, identify the
  unproved arithmetic statement, and PARK without a no-cycle claim.

### Authorized continuation (9 September 2026)

Mathematical target: Does every exact S_b cycle meet its wrong-parity set, uniformly in b>=3?

Novelty hypothesis: The union of periodic points, interlacing of its cycles, and exact unit-width floor cells may constrain parity in a way single-cycle geometry does not.

Falsifier: Common rotation and smooth spacing persist under a parity-correct one-unit successor alteration, or rotation comparison is non-strict without a common exact cycle.

Already killed by?: Coarse surplus/charge and local-cell-only arguments are closed. This continuation was explicitly requested and tests a global relation between complete cycles and a precise rounding boundary; no floor or band survey is reopened.

Existing machinery: Cubic-band rank rotation and old exact data; independent AI audit; elementary finite permutations; exact roots and logarithmic defect identity.

Maximum Phase-0 scope: Written common-period/interlacing, sorted-grid and one-unit rounding proofs; complete old small graphs at b=3,9,29; rounding controls at b=3,9,29,101 and the single exact R_11 branch-offset witness; exact boundary checks at arbitrarily large symbolic sizes. No larger trajectory census or Lean packaging.

Promotion criterion: A proved uniform exact-parity obstruction. Structural statements can be recorded separately without asserting that criterion is met.

Stop criterion: If the exact parity inequality remains unproved, record the valid statements and precision obstruction with PARK. Do not automatically open another attack.

## Balanced-ternary formulation

All states are ordinary positive integers. Canonical balanced ternary
can represent them but does not enter the proof.

## Why BT may be relevant

No representation advantage is used. This remains a Juggler research
module and introduces no dependency in the core `bt` package.

## Candidate operations / invariants

The invariant is the cyclic order of the complete finite orbit. The
even images occupy the lowest ranks and the odd images the highest.
The rank increment is the number of even states. Individual inverse
cells alone do not establish this permutation structure.

No uniform obstruction to (4) was proved. The witnesses show that the
parity-relaxed constraints coexist, and that exact closure does not by
itself establish (4). A wrong-parity example neither proves nor refutes
the assertion that every such cycle has a wrong-parity state. The
follow-up instead tests global cycle relations and absolute rounding
precision. No statistical parity assumption is made.

## Experiments

Probe: `research.juggler_sequence.cycle_cubic_band`.
Data: [summary.json](../../data/research/juggler/cycle_cubic_band/summary.json).
Tests: [test_cycle_cubic_band.py](../../tests/research/juggler_sequence/test_cycle_cubic_band.py).
Regenerate with `python -m research.juggler_sequence.cycle_cubic_band`.

The probe uses arbitrary-precision integers and `math.isqrt`.
The explicit control cycles additionally receive an independent
certificate \(y^2\le x^h<(y+1)^2\), with \(h=3\) or \(1\).

| Scope | Exact finite outcome |
|---|---|
| Every state of \(I_b\), \(3\le b\le30\) | 38 primitive cycles across 28 threshold maps; all pass the order checks and fail actual parity compatibility |
| Orbit starting at \(b\), \(3\le b\le10000\) | 9,998 eventual cycles; all pass rank rotation, coprimality, mechanical-word, exact-edge and expansion checks; none is a Juggler cycle |
| Same 9,998 starts | 1,355 are periodic from the initial state; the others have a transient |
| Longest observed cycle | \(b=9385\), minimum 9392, maximum 826579131129, length 16631, odd-branch count 10493, parity mismatches 8310 |
| \(b=350000001,1000000007,1000000000039,1000000000000000003\) | No repeat within the specified 200,000-step cap for each; all four are unresolved computations |

One sampled orbit is not a complete graph survey. The 9,998 rows are
not claimed to represent distinct cycles across different thresholds.
The complete small-graph count is likewise a count across maps.
The large capped runs are not evidence of escape: Proposition 2
proves that they eventually repeat. No cap or parity-frequency
observation is promoted into an infinite statement.

### Continuation: small independent controls

Regenerate only the continuation with
`python -m research.juggler_sequence.cycle_cubic_band --followup`.
Data: [followup.json](../../data/research/juggler/cycle_cubic_band/followup.json).
The former large capped runs were not extended and the former census
was not enlarged. All edge, projection-boundary and interlacing checks
use integers. Twelve log-log grid checks use 80-decimal arithmetic as
numerical consistency checks, not rigorous interval certificates; the
quantified bounds are proved below.

| Map and parameter | Cycles / period / relevant checks |
|---|---|
| Complete S_3 periodic set | 2 cycles, common period 3, 6 points interlacing |
| Complete S_9 periodic set | 2 cycles, common period 11, 22 points interlacing |
| Complete S_29 periodic set | 3 cycles, common period 19, 57 points interlacing |
| R_3, one orbit | Period 3; 1 one-unit alterations; not an actual Juggler cycle |
| R_9, one orbit | Period 14; 8 one-unit alterations; not an actual Juggler cycle |
| R_11, one orbit | Period 11; 7 one-unit alterations; not an actual Juggler cycle |
| R_29, one orbit | Period 49; 25 one-unit alterations; not an actual Juggler cycle |
| R_101, one orbit | Period 141; 72 one-unit alterations; not an actual Juggler cycle |

The branch-offset control is the exact R_11 cycle in Proposition 6.
Its integer square-cell margins and all same-branch image differences
are checked independently of the 80-decimal grid calculations.

## Conjectures

No new conjecture file is opened. The desired global no-cycle theorem
remains unproved. The precise missing step within this height class
is stated under Open questions.

## Counterexamples

**Correct closure and word, incorrect parity.** At \(b=9\), (3) has
the exact primitive closed orbit
\[
9,27,140,11,36,216,14,52,374,19,82,9.
\]
Its word is \(OOEOOEOOEOE\), its counts are \((L,o)=(11,7)\),
its minimum is odd, its maximum is even, and \(374<9^3\).
It has no \(EE\) or \(OOO\), and \(3^7>2^{11}\).
Nevertheless the prescribed odd branch is used at the even states
36, 14 and 52. In the actual map, for example, \(J(36)=6\),
whereas \(S_9(36)=216\). This is not a Juggler cycle.
It also refutes a blanket claim that at least one third of each
threshold cycle must have the wrong parity: here the fraction is
\(3/11\). No weaker positive fraction has been proved.

**The height hypothesis matters to the order argument.** The
prescribed word \(OOOEOE\) closes exactly on
\[
3,5,11,36,6,14,3.
\]
All six states before return are distinct, while
\(\gcd(6,4)=2\) and \(36>3^3\). This word is not the ceiling word
for \((6,4)\). Only the step at 6 uses the wrong parity:
\(\lfloor\sqrt{6^3}\rfloor=14\), whereas \(J(6)=2\).
This refutes the parity-relaxed extension without the height bound;
it is not a counterexample to any theorem about actual Juggler cycles.

## Formalization

**EXACT — LEAN VERIFIED** for the six consolidated results at their stated
scope. The seven Cubic modules are imported by the Paper A barrel. The
[formalization map](../theory/juggler_finite_dynamics_formalization.md)
identifies their declarations and distinguishes the illustrative asymptotic
comparison from the compiled inequalities. Separate AI audits preceded
formalization; no independent human review or external priority is claimed.

## Results

Statements and written proofs have one editorial home:
[Paper A, Section 3.10](../theory/juggler_finite_dynamics_note.md).
This supersedes the earlier copied proofs in this dossier. The finite
controls remain supporting data and do not prove universal parity failure.

## Open questions

The authorized absolute-cell follow-up is recorded in
[Absolute floor cells](juggler_cycle_absolute_cells.md). It adds three
written necessary restrictions or comparison obstructions; none establishes
uniform wrong parity. Paper A remains the canonical proof source for the
six Lean-supported results consolidated above.

For \(b\ge3\), define the wrong-parity set
\[
B_b=\{x\in I_b:x<b^2\text{ and }x\text{ even}\}
\ \cup\ \{x\in I_b:x\ge b^2\text{ and }x\text{ odd}\}.
\]
The exact missing arithmetic statement is that every cycle of
\(S_b\) intersects \(B_b\), for every \(b\ge3\).
Equivalently, every orbit of \(S_b\) eventually visits \(B_b\).
This would exclude all actual Juggler cycles with \(M<m^3\):
use \(b=m\). Conversely, a cycle of \(S_b\) avoiding \(B_b\)
would be an actual Juggler cycle whose minimum \(r\ge b\) and
maximum \(<b^3\le r^3\) satisfy that height condition.

The order lemma proves no such intersection. The measurements do
not prove parity independence or any uniform discrepancy estimate
on this sparse cycle-selected set. An estimate over consecutive
integer starts would not automatically apply to it. Even a proof
of this missing statement would still leave the separate regime
\(M\ge m^3\) unresolved.

## Decision

**PARK.** The continuation proves the common-period/interlacing and
sorted-grid results, plus two precisely scoped obstructions to weakening
the rounding or retaining only branchwise gaps. The exact wrong-parity
intersection is not proved. The valid statements are retained; no larger
census, new floor or automatic follow-on attack is authorized by this
decision. Exactly one next mathematical question remains: prove that
every exact threshold cycle meets B_b, using absolute unit-cell alignment
or a constraint coupling the branch offsets that the gap equations erase.
The regime M>=m^3 remains a separate unresolved part of no-cycle.

## Publication assessment

Status: **STRUCTURAL**. This is a separate research record with
AI-assisted written proofs, not a publication-ready no-cycle proof.
Paper A's released title, sources, PDF and certified period bounds
remain unchanged by this attempt.

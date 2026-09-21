# m-cycles of the 3n−1 map: the Simons–de Weger template on the negative side

Status: **PROMOTE** (a theorem with one external input; published as Paper D, [doi:10.5281/zenodo.22876190](https://doi.org/10.5281/zenodo.22876190))

Standalone phase on the Collatz bridge, following
[juggler_negative_floor_3x1](juggler_negative_floor_3x1.md) and
[juggler_collatz_finance_mirror](juggler_collatz_finance_mirror.md). Not a halt theorem for
either map, not a Juggler cycle exclusion, and not a change to \(N_0\). The manuscript is
[collatz_3n_minus_1_m_cycles_note.md](../theory/collatz_3n_minus_1_m_cycles_note.md).

## Problem

The \(3n-1\) map \(g(y)=y/2\) (\(y\) even), \((3y-1)/2\) (\(y\) odd) on the positive integers
is the shortcut \(3n+1\) map read on the negative integers. Its known cycles are \(1\),
\((5,7,10)\) and the eleven-element cycle at \(17\), and every start below \(2^{51}\) reaches
one of them (the laboratory's certificate: CPU to \(2^{44}\), GPU to \(2^{51}\), 21 September
2026). An \(m\)-cycle is a cycle with \(m\) odd runs,
equivalently \(m\) local minima. Simons 2007 proves there is exactly one nontrivial 2-cycle,
floor-free, and says his method stops at \(m\ge3\); Simons–de Weger 2005 and Hercher 2023
exclude \(3n+1\) \(m\)-cycles for \(m\le68\) and \(m\le91\) from verification floors; nobody
has run that template on \(3n-1\), because nobody had a floor there. Run it.

## Exact statement

For which \(m\) does the \(3n-1\) map have no \(m\)-cycle whose least element is at least
\(2^{51}\), hence (by the floor) no \(m\)-cycle other than the two known ones with an even
step? What does each larger floor buy, and which lengths \(K\) does the template leave at
the first open \(m\)?

## Current literature

- `simons-2007-inductive-two-cycles-3x1`, read in full: exactly one nontrivial 2-cycle of
  \(3x-1\), at \(17\), floor-free; the method stops at \(m\ge3\). **known**; the note's
  \(m\le2\) rows reprove a weaker, floor-dependent form of it.
- `simons-2008-m-cycles-generalized-syracuse`, read in full: the five-step template (floor,
  cycle-equation bound on \(\Lambda\), Crandall's lemma, Rhin's bound, lattice reduction),
  applied to \(3x+q\), \(px+q\), Guy's permutation and the Roelants problem; nothing on
  \(3x-1\). **extended**: the template transposed, with the negative-side constants derived
  here.
- `simons-de-weger-2005-collatz-m-cycles`, read in full on 21 September 2026 from the PDF
  Philippe fetched: \(m\le68\) for \(3n+1\) at \(X_0=301\cdot2^{50}>3.3889\cdot10^{17}\)
  (Roosendaal, November 2004), by three stages, tables (Lemma 15: \(57\)), the
  continued-fraction reduction through the champion partial quotients (Lemma 17: \(63\)) and
  de Weger's approximation lattice (Lemma 18: \(68\)); the \(75\) is Simons 2008 at the later
  floor. **extended**: their Section 7 lattice is a two-dimensional approximation lattice
  whose short points are the \((K,L)\) pairs in the Corollary 5 window below the ceiling,
  each then tested against Corollary 5 and Lemma 7; the three-gap walk produces that list and
  the probe applies those two tests, so the fifth step is not open. Run on their side at their
  floor, the machinery reproduces their Lemma 18 to the unit (none for \(64\le m\le68\), their
  five pairs at \(69\le m\le72\) with their killing floors to rounding). On the \(3n-1\) side
  the same floor gave \(63\) before Lemma 6 and gives \(69\) after it: the five values are
  the sign, not a stage. Their \(68\) is not the right yardstick for the refined machinery,
  because their 2005 work predates the valley argument entirely; the comparison that means
  something is Hercher's. (A first reading on 21 September had called the transposition
  "their Lemma 17 exactly" and the lattice "worth five values of \(m\)"; corrected the same
  day.)
- `rhin-1987-pade-irrationality`, read at its Proposition on 21 September 2026:
  \(|u_0+u_1\log2+u_2\log3|\ge H^{-13.3}\) for \(H=\max(|u_1|,|u_2|)\ge2\), no further
  constant. The form \(e^{-13.3(0.46057+\log K)}\) carried since Paper A is [SdW] Lemma 12,
  the same bound at \(H=K+L\) in the odd count; the probe now uses (7) at \(H\) the length.
- `hercher-2023-collatz-m-cycles`, read from the PDF: \(m\le91\) for \(3n+1\) at
  \(695\cdot2^{60}\), with the valley arrangement and Lemma 8. **extended**; the valley
  arrangement behind his Main Theorem 21 is transposed as Lemma 6 of Paper D 1.1.0, worth
  three values of \(m\) at \(2^{51}\) and seven at \(2^{68}\), where the plain template
  gave \(82\) and the refined one gives \(89\). Run on his side at his own floor the six
  lemmas give \(90\) against his \(91\), which is the calibration that says the
  transposition is faithful and also says a little is lost in it. His two m-free refinements,
  Theorem 27 and Corollary 29, were measured and do not reach; see
  [negative_knowledge.md](../negative_knowledge.md).
- `sinisalo-2003-collatz-minimal-cycle-lengths`: Table 2 is the \(m\)-free survivor table on
  this side. **known**.
- Prior-art search by name, 21 September 2026: "3x−1 problem" cycles, "3n−1" negative Collatz
  cycles 2025–2026 on arXiv; nothing beyond the records above. The two earlier sweeps for a
  \(3x-1\) floor (19 and 20 September) found none in print.

## Branch budget

- **Target:** the largest \(M\) such that no \(m\)-cycle with \(m\le M\) exists above the
  \(2^{51}\) floor, by the Simons–de Weger template with negative-side constants.
- **Novelty hypothesis:** the first \(m\)-cycle theorem for \(3n-1\) with \(m\ge3\), and the
  first floor to feed one.
- **Falsifier:** a real cycle failing the inequalities — the template must leave the
  \(17\)-cycle's length \(11\) at \(m=2\) when the floor is set at \(17\), and the
  \((5,7,10)\) length \(3\) at \(m=1\) with the floor at \(5\).
- **Already killed by?:** none. The finance-mirror cluster reproduced Eliahou and Hercher on
  the positive side and priced the negative side as a table; the floor branch supplied the
  floor; neither ran the \(m\)-cycle step, and the journal of 20 September named it the best
  next question.
- **Existing machinery:** `neg_cycle_finance`, `neg_prefix_noncontracting`,
  `neg_cycle_expanding` (Lean, `CollatzBridge.lean`); `lambda_juggler`, the continued
  fraction of \(\log2/\log3\) and the three-gap walk (`collatz_finance_mirror`); the floor
  certificate (`negative_floor_3x1`).
- **Maximum Phase-0 scope:** the tables at the five floors and the survivor lengths at the
  first open \(m\).
- **Promotion criterion:** \(M\ge3\) with the known cycles surviving the same test.
- **Stop criterion:** a negative-side constant that does not carry, or an admissible length
  the tower cannot reach at every \(m\ge3\).

## Balanced-ternary formulation

Not used. The objects are the parity word of a cycle and the linear form
\(o\log3-K\log2\).

## Why BT may be relevant

It is not; recorded for the template.

## Candidate operations / invariants

The run identity \(g^k(y)-1=(3/2)^k(y-1)\), the run length \(v_2(y-1)\), the cycle product
\(3^o2^{-K}\prod(1-1/(3y))=1\), the chaining \(u_{i+1}<u_i^{\delta}/2\) with
\(\delta=\log_23\), the three-gap walk for the admissible lengths, Rhin's ceiling. All
**EXACT — HUMAN PROOF** in the note except Rhin (external) and the window enumeration (exact
arithmetic at 80 digits).

## Experiments

`python -m research.juggler_sequence.negative_m_cycles` writes
`data/research/juggler/negative_m_cycles/summary.json` and
[juggler_negative_m_cycles.md](../research/juggler_negative_m_cycles.md): per floor and per
\(m\), the bound on \(\Lambda\), Rhin's ceiling \(K_3(m)\), the admissible lengths below it,
the least one \(K_0(m)\), the closest margin in bits and the survivors; and, on the \(3n+1\)
side at [SdW]'s floor, their Lemma 18 rows for \(64\le m\le72\).

`python tools/check_3n_minus_1_note_numeric.py` recomputes the manuscript's numbers by a
route independent of the probe: an integer sieve over \(K=iQ+j\) for the admissible lengths
at \(2^{40}\), \(2^{44}\) and \(2^{48}\) (checked first against a direct scan at coarse
windows), the ceilings from their defining inequality at \(K_3-1\) and \(K_3\), the margins
at one hundred digits, the known cycles by iteration, the floor's printed counts against the
certificate; it compares them with the note's tables and the summary, writes
`manuscript_check.json` beside the summary, and fails on a copy of the note with two wrong
cells (21 September 2026: two findings, nothing else). `python tools/build_paper_d.py`
builds [collatz_3n_minus_1_m_cycles_note.pdf](../../juggler_review/collatz_3n_minus_1_m_cycles_note.pdf)
(eight pages) with the Paper C chain and a strict layout gate, writes the manifest
`docs/theory/paper_d_release.json`, the Zenodo metadata and the deposit kit; `--check`
verifies every generated copy, and the release gate calls it on the live repository.

## Conjectures

None. The \(3n-1\) analogue of the Collatz conjecture, that \(1\), \(5\) and \(17\) are the
only cycles and no orbit diverges, is not a laboratory conjecture and is not touched.

## Counterexamples

The known cycles are the witnesses that the inequalities are sound: with the floor at their
least element they pass every test, and with the floor one above it they do not.
`tests/research/juggler_sequence/test_negative_m_cycles.py`.

## Formalization

**Lemmas 1 and 3 are Lean** (21 September 2026): `Problems.Collatz.NegativeMCycles`, twenty
declarations, in the `Problems` barrel so the default build covers them. Thirteen depend on
Mathlib's three standard axioms, five on none at all (the `decide` computations on the known
cycles), two are derived; no `sorry`, no `native_decide`.

The formalization writes the start of an odd run as \(y=2^a m+1\) with \(m\) odd, which
removes every truncated subtraction and puts the run in closed form
(`negT_run_iter`: \(g^k(2^a m+1)=3^k2^{a-k}m+1\) for \(k\le a\)). Lemma 1's clauses are
`negT_run_odd`, `negT_run_even`, `negT_start_ge`, `negT_localMax`, packaged at an odd start
by `negT_lemma_one` with the \(v_2\) decomposition `negT_run_decomp`; Lemma 3 is
`negT_chain_nat` (the integer half, \(2u'<3^am\)) and `negT_chain_real` (the exponent,
\(u'<u^{\delta}/2\)), packaged as `negT_lemma_three`. The three known cycles and the sign of
the map are checked inside the kernel (`negT_sign_is_minus`, `negT_cycle_seventeen`,
`negT_chain_tight_at_17`: \(2\cdot40<81\), one unit of slack, which is the note's tightness
remark). Guard test `tests/research/juggler_sequence/test_negative_m_cycles_lean.py`.

**What formalizing changed.** The closed form needs no parity assumption on \(m\): the powers
of two alone keep the state odd through the run, and oddness enters only to know the run
stops at \(a\). The hypotheses of `negT_run_iter`, `negT_run_odd` and `negT_localMax` are
correspondingly weaker than the note's Lemma 1 as written.

**Not formalized.** Lemma 2, whose content is the cycle equation and the bound on
\(\Lambda\), both real-analytic. Its first clause \(\Lambda>0\) is `neg_cycle_expanding` on
the conjugate side, with `neg_cycle_finance`, `neg_prefix_noncontracting` and
`neg_cycle_word_is_juggler_shape` in `CollatzBridge.lean`; the conjugation \(x=-y\) that
carries one side to the other is not itself formalized, because `Problems.Collatz` sits below
`Problems.Juggler` and importing the bridge from it would invert the layering. It belongs in
the Paper D barrel, which does not exist yet. Rhin's bound would enter as a hypothesis, as
`cycleMin_length_of_rhin` does on the Juggler side.

## Results

- **Theorem (EXACT — HUMAN PROOF, one external input), version 1.1.0.** Given Rhin's bound,
  the \(3n-1\) map has no \(m\)-cycle with \(1\le m\le61\) whose least element is at least
  \(2^{51}\); with the floor, none with \(m\le61\) other than \((5,7,10)\) and the cycle at
  \(17\). For \(m\le52\) no admissible length lies below Rhin's ceiling at all; for
  \(53\le m\le61\) each admissible length fails one of Theorem 8's two displays, the
  chaining or the valley count, the closest with \(0.1\) bits to spare at \(m=61\),
  \(K=83130157078217\) -- which is the length that survives one row later with \(0.3\)
  bits. The theorem is delicate at its top end and the two figures say so. The m-free period
  bound at \(2^{51}\) is unchanged at \(85137581\) with \(53715833\) odd steps.
- **Version 1.0.0 of the paper, superseded but correct.** Without the valley count the same
  floor gives \(m\le58\), the closest exclusion by \(9.8\) bits at \(m=58\),
  \(K=64789416887513\), and two lengths open at \(m=59\). The first draft's floor
  \(2^{44}\) gave \(m\le49\), the closest by \(1.4\) bits at \(K=757698850864\).
- **The floors (COMPUTATIONALLY VERIFIED).** With both displays: \(2^{40}\): \(m\le49\);
  \(2^{44}\): \(51\); \(2^{48}\) and \(2^{49}\): \(58\); \(2^{50}\): \(59\);
  \(2^{51}\): \(61\); \(2^{56}\): \(68\); \(301\cdot2^{50}\), [SdW]'s floor: \(69\)
  on this side against their \(68\) on theirs, though that comparison is the wrong one --
  their 2005 work predates the valley argument, and the calibration that means something is
  Hercher's; \(2^{60}\): \(74\); \(2^{68}\): \(89\). Without the valley count the same
  rows read \(44\), \(49\), \(49\), \(54\), \(56\), \(58\), \(63\), \(63\),
  \(68\), \(82\). The rows at \(2^{49}\), \(2^{50}\) and \(2^{51}\) were also sieved
  independently, by a checker carrying its own implementation of the valley cap written from
  the manuscript rather than imported from the probe.
- **What the template left at \(m=50\), floor \(2^{44}\), before Lemma 6:** the lengths
  \(539722056247\), \(757698850864\), \(975675645481\), \(1193652440098\), with \(22.4\),
  \(15.0\), \(7.8\), \(2.9\) bits of room; at \(2^{48}\) only the last. They are the output of
  the template's last step, not its input; the floors that remove them are \(2^{44.01}\),
  \(2^{44.57}\), \(2^{45.48}\) and \(2^{48.58}\).
- **Sanity.** With the floor at \(17\), \(m=2\) leaves \(K=11\); at \(5\), \(m=1\) leaves
  \(K=3\); the chaining is tight on the \(17\)-cycle (\(16\to40\) against \(40.5\)).
- **What the template left at \(m=59\), floor \(2^{51}\), before Lemma 6:** the lengths
  \(64789416887513\) and \(83130157078217\), with \(12.4\) and \(5.0\) bits of room,
  removed by raising the floor to \(2^{51.87}\) and \(2^{55.18}\). Lemma 6 removes both at
  \(2^{51}\), and the first open \(m\) moves from \(59\) to \(62\).
- **The floor to \(2^{51}\) (COMPUTATIONALLY VERIFIED, 21 September 2026).** The GPU sweep of
  \([2^{44},2^{51})\) in 8 chunks, 59 minutes on the RTX 5090: \(1117103813820416\) odd starts,
  coverage exact, no failure, no new cycle, no overflow, greatest step count \(847\), peak about
  \(2^{97.0}\). Three \(2^{37}\) spot windows agree with the archived CPU jump walker under WSL:
  same walked and skipped counts, same peaks, the GPU's exact step counts below the CPU's
  granular ones by 72, 12 and 48. Record `gpu_runs.json`, checks
  `gpu_calibration/` under `negative_floor_3x1`.
- **Ceilings corrected (21 September 2026, by the manuscript check).** The probe's
  \(K_3(m)\) was one above the least integer of its definition: it evaluated \(L_{\min}\)
  at \(\lfloor K\rfloor\) inside a real bisection and rounded up. It is exact now; Table 1
  of the note moved down by one in every row, and nothing else moved, the admissible counts,
  least lengths, margins and survivors being the same at every floor.
- **The fifth step is not open (21 September 2026, second pass).** [SdW] Section 7, re-read:
  the approximation lattice lists the admissible pairs and each is "checked for fulfilling
  Corollary 5 and Lemma 7", which is what the probe has done since 20 September. Proof by
  reproduction on their side: with the window on the contracting side at \(301\cdot2^{50}\),
  none for \(64\le m\le68\); at \(m=69\) the pair \((5750934602875680,3364081086781987)\)
  falling at \(576.2\cdot2^{50}\) against their \(577\); the same pair at \(584.6\), \(592.9\),
  \(601.3\) for \(m=70,71,72\) against \(585\), \(593\), \(602\); their second pair at
  \(623.6\), \(632.4\) against \(624\), \(633\); their three \(m=72\) pairs at \(308.2\),
  \(666.8\), \(705.3\) against \(309\), \(667\), \(706\). One point more at \(m=72\), the
  double of their second pair (\(0.9\) bits of room, \(316.2\cdot2^{50}\)), which their table
  does not carry. Their Lemma 7 constant \(c_m\) is, algebraically, the
  \(2^{-(B-m)/((\delta-1)B)}\) of the note's Lemma 3.

## The valley-count refinement: Lemma 6 of the paper, m <= 61 at the same floor

**Derived 21 September 2026**, transposing the arrangement behind Hercher's Main Theorem 21.
The three lemmas are three constraints and one objective on the same vector
\(b_i=\log_2 u_i\) over the local minima of an \(m\)-cycle:

| | |
|---|---|
| floor | \(b_i\ge L_0=\log_2(X_0-1)\) |
| chaining (Lemma 3) | \(b_{i+1}\le\delta b_i-1\) |
| odd steps (Lemma 1, summed) | \(\sum b_i\ge o\) |
| objective (Lemma 2) | \(\Lambda<\sum 2^{-b_i}\) |

The note relaxes this twice over: Lemma 2 puts every minimum at the floor and gets
\(\Lambda<m/(X_0-1)\), Lemma 3 drops the objective and gets \(L_0\ge o/B(m)\). Both are
loose at once, because a cycle cannot have all its valleys at the floor *and* carry \(o\)
odd steps: the chaining caps how fast the minima climb away from the floor. Keeping the
system intact is the refinement.

The feasible set is a polytope and \(\sum2^{-b_i}\) is convex, so its maximum sits at a
vertex: a block of \(r\) minima at the floor, one free coordinate, the rest on the chaining
ceiling. `valley_cap(m, o, X0)` maximizes over \(r\); a length is excluded when its
\(\Lambda\) already exceeds that maximum.

**Result at the verified floor \(2^{51}\): \(m\le61\)**, against \(m\le58\) from the
separate relaxations. The two lengths open at \(m=59\) and \(60\) fall, and so do the four
at \(61\); one length, \(83130157078217\), survives at \(m=62\) with \(0.3\) bits. Three
values of \(m\) gained by argument, with no change to the floor, and between two and seven
at every other floor in the table: the ladder reads \(49\), \(51\), \(58\), \(58\),
\(59\), \(61\), \(68\), \(69\), \(74\), \(89\) where it read \(44\), \(49\),
\(49\), \(54\), \(56\), \(58\), \(63\), \(63\), \(68\), \(82\).

**The calibration that makes it credible.** Run on the \(3n+1\) side at Hercher's own floor
\(695\cdot2^{60}\), the same six lemmas exclude \(m\le90\) against the \(m\le91\) of his
Main Theorem 23. One short of a published result reached by the same idea.

**Known-bad input.** With the floor set at their own least element, \((5,7,10)\) and the
cycle at \(17\) both still clear the cap, so the refinement is not excluding the truth. The
cap is also checked never to exceed Lemma 2's \(m/(X_0-1)\), so it can only help.

**Status: written as Lemma 6 of version 1.1.0**, with a proof that needs no vertex
enumeration. The first derivation maximized the objective over the polytope's vertices and
argued the maximizing family; the published form instead takes the bound through a threshold
\(T\), bounds how many minima can sit below it, and minimizes over \(T\). The minimum is
exact, not a grid: the bound is piecewise in \(T\) with breakpoints
\(T_r=(o+A_{m-r})/(r+B_{m-r})\), and on each piece it falls with \(T\). At \(T=L_0\) it
is Lemma 2, so it is never weaker. Version 1.0.0 states \(m\le58\) and remains correct.

Pinned: `valley_cap`, `valley_excluded`, `valley_refined` in the probe;
`test_the_valley_refinement_spares_the_cycles_that_exist` and
`test_the_valley_refinement_closes_three_more_values_of_m`.

## Hercher's Corollary 29 transposed: the mechanism carries, the constant is the wrong one

**Measured 21 September 2026**, after Lemma 6 had moved the first open value to \(m=62\)
and made the arithmetic of Corollary 29's \(1.30\) bits look sufficient. It is not, and the
reason is not arithmetic.

*The negative-side Lemma 26.* Lemma 1 makes the run exact, so the run from a local minimum
\(y\) with \(u=y-1\) and \(a=v_2(u)\) contributes
\(T(y)=\sum_{k<a}1/(3g^k(y)-1)<\kappa(a)/u\), \(\kappa(a)=1-(2/3)^a\). That factor is what
Lemma 2 throws away and what Hercher's Remark 7 keeps as \(3(1-(2/3)^k)/n\); the relation
between consecutive minima is \(u_i=(2/3)^{a_i}(2^{r_i}(u_{i+1}+1)-1)\) against his
\(n_i=(2/3)^{k_i}(2^{\ell_i}n_{i+1}+1)-1\), the same shape with the sign flipped. His one,
two and three-run averaging therefore carries case for case, with the same rationals. The
residue drop carries too, and sharper: Lemma 5 makes each case word a residue class, and
because every minimum of a window is above the floor, the drop uses the least member of the
class *above the floor*.

*What it is worth here.* Corollary 29 improves the m-free constant of Theorem 27, and the
open values of this note are not decided by any m-free bound — at \(m=62\) the chaining
display clears by \(41.4\) bits. What holds the row open is Lemma 6's cap, which is
minimised with four minima at the floor at \(m=62\) and five at \(m=63\), and averaging can
act on nothing but that block. Write \(\rho(y)=T(y)(X_0-1)\in[0,1]\), the valley's
contribution in units of Lemma 2's own one-per-valley.

| block | needed at | \(\rho\) average demanded | attained above \(2^{51}\) | start of the window | delivered / needed (bits) |
|---|---|---|---|---|---|
| 1 | — | — | \(0.999999999\) | \(2^{51}+1\) | \(0.000\) |
| 4 | \(m=62\) | \(0.8137\) | \(0.9013\) | \(2255557997555713\) | \(0.150/0.297\) |
| 5 | \(m=63\) | \(0.6509\) | \(0.8689\) | \(2266848965985921\) | \(0.203/0.619\) |
| 6 | \(m=64\), first of its two survivors | \(0.5424\) | \(0.7992\) | \(2343202629650049\) | \(0.323/0.882\) |
| 7 | — | — | \(0.7703\) | \(2258052872963713\) | \(0.376\) |

The second survivor at \(m=64\) is worse still: its block is a single minimum, which demands
\(0.2512\) against an attainable \(1.0\).

The attained column is concrete integers, each walked on the map, so it bounds from below
what any averaging argument can give; the demanded column charges the method no boundary
loss at all. It is short by rather more than the rounding: **just over half of what
\(m=62\) needs and a third of what \(m=63\) needs.** The windows are orbit segments, not
segments of a known cycle — none is known above the floor — so they refute the method and
not the conclusion; that is the right target, because Lemma 26 and Corollary 29 use only the
floor and the local step relations along a few consecutive runs and never the cycle's
closure, and these windows satisfy every local constraint, their runs summing to thirty
against an \(o\) of \(5.2\cdot10^{13}\). The reason the block matters so much is
the 2-adic budget: \(d\) minima near the floor must fit their runs and halvings into the
floor's \(51\) bits, which forces short runs, and short runs waste \(\kappa\). One minimum
alone is worth nothing at all, because \(2^{51}+1\) has \(a=51\).

**Known-bad input.** Set the floor at a real cycle's own least element and the window
ceiling must still leave room for that cycle's minima. It does, and barely: at \(17\) the
two minima sit at \(0.541975\) against a ceiling of \(0.541992\), and at \(5\) the single
minimum sits at \(5/9\) against \(0.5556\). Scaling \(\kappa\) by \(99/100\) makes the
ceiling exclude both, which is the check the bound was run against before it was believed.

**Status: CLOSE at this floor.** Recorded in
[negative_knowledge.md](../negative_knowledge.md) under the Hercher heading. Nothing enters
the manuscript, because nothing there moves. At \(2^{60}\) the same measurement is within
\(0.008\) bits at \(m=76\) and undecided at \(m=75\), so it is worth remeasuring before that
floor is run.

Pinned: `research.juggler_sequence.negative_valley_windows` (support module, not a probe and
not an input of Paper D's release manifest);
`test_herchers_lemma_26_transposes_and_its_window_bound_spares_the_real_cycles`,
`test_a_stronger_run_factor_excludes_the_cycles_that_exist`,
`test_herchers_corollary_29_transposes_but_improves_the_wrong_constant` and
`test_the_window_witnesses_sit_on_the_residue_trees_ceiling`.

## Open questions

- The floor stands at \(2^{51}\) since the GPU sweep of 21 September 2026. With Lemma 6 in
  force, \(2^{52}\) to \(2^{55}\) still buy nothing; \(2^{56}\) (about 32 hours of the
  card) buys seven values at once, \(m\le68\), and \(2^{60}\) (about 21 days) buys
  \(74\). Verifier, driver, calibration and sweep records are archived with
  `negative_floor_3x1`.
- Hercher's valley arrangement (his Main Theorem 21) **transposed on 21 September 2026**,
  and worth three values of \(m\) at \(2^{51}\): it is Lemma 6 of version 1.1.0, proved
  through a threshold rather than the vertex argument the first derivation used, and the
  section above records both. What remains open is the last value: at Hercher's own floor
  these lemmas give \(90\) where he publishes \(91\), and closing that gap means reading
  his arrangement more closely than the transposition did. His other two m-free refinements
  were read from the source on
  21 September 2026 and measured: Corollary 29's residue tracking gains \(1.30\) bits of
  effective floor where \(4.18\) are needed to close \(m=59\), and Theorem 27's constant is
  \(0.23\) bits tighter than this side's kernel-checked one and leaves the period bound at
  \(85137581\). Both are recorded as method walls in
  [negative_knowledge](../negative_knowledge.md); do not reopen them.
- The Eliahou-type period lattice on this side at \(2^{44}\).
- Their Lemma 7 constant \(c_m\to0.30576\) against the \((B-m)/(\delta-1)\) term here, a
  bookkeeping comparison that would move nothing at \(2^{44}\) but is owed to the note.

## Decision

`PROMOTE`. The template carries with the sign flipped, the constants improve rather than
worsen (the odd step subtracts), and the result is a theorem nobody has stated about a map
the literature names but has not verified; on their side at their floor it reproduces their
Lemma 18 to the unit. Best next question: the floor to \(2^{56}\), a weekend of the card, then Hercher's valley
arrangement.

## Publication assessment

Status: `PUBLISHED`, with **version 1.1.0 built and not yet deposited**. The record is
**Paper D**, deposited 21 September 2026 as *No m-cycles of the 3n−1 map for m ≤ 58*,
version 1.0.0, nine pages, at the floor \(2^{51}\): version DOI
[10.5281/zenodo.22876190](https://doi.org/10.5281/zenodo.22876190), concept DOI
[10.5281/zenodo.22876189](https://doi.org/10.5281/zenodo.22876189), deposited file
byte-identical to the kit copy at the time, md5 `c6f6f662016ca30a859bf57b0cc81793`, checked
against the record after deposit.

Version 1.1.0, *No m-cycles of the 3n−1 map for m ≤ 61*, adds Lemma 6 and is built, gated and
checked here; it goes up through the record's new-version operation, which keeps the concept
DOI resolving to the latest. The kit at
[juggler_review/zenodo_paper_d/](../../juggler_review/zenodo_paper_d/) now holds 1.1.0's
files, so the kit PDF is no longer the deposited bytes; 1.0.0's are recoverable from the
record and from the commit that carried them.

**Ready.** The theorem and its margins; every number recomputed by an independent route,
the valley cap included, from a second implementation written off the manuscript rather than
imported; the floor as a two-implementation certificate with spot checks; Lemmas 1 and 3
machine-checked, and they are exactly the two the valley count consumes; the builder, the
manifest, the Zenodo metadata and the kit, all under the release gate; the front and back
matter (classification, keywords, AI disclosure, responsibility statement, availability) as
Papers A–C carry them; every reference cited, the three-distance theorem attributed, and
every internal path pinned to a public commit.

**What makes the new lemma credible rather than merely convenient.** Run on the \(3n+1\)
side at Hercher's own floor \(695\cdot2^{60}\), the same six lemmas exclude \(m\le90\)
against his published \(m\le91\): one short of a refereed result reached by the same idea.
Run against the cycles that exist, with the floor at their own least element, the cap spares
both \((5,7,10)\) and the \(17\)-cycle. And the cap is checked never to exceed Lemma 2's
\(m/(X_0-1)\), which is the bound it refines.

**Still open after publication.** No independent human has read the proofs; every check is
the author's or mechanical. The floor is the laboratory's own and is not deposited as a
citable dataset of its own. The floor stands at \(2^{51}\); \(2^{56}\) would now give
\(m\le68\) for about thirty-two hours of the card, and would be a further version of the
record rather than a correction. Lemma 2 is not in Lean, and the note says why; nor is
Lemma 6, which is arithmetic on top of Lemmas 1, 2 and 3.

**What a referee is still most likely to ask.** Why the floor stops where it does, since the
sweep is cheap; whether the \(m\)-free row should be compared with Sinisalo's table in more
detail than one sentence; and why the valley count reaches \(90\) where Hercher reaches
\(91\), which is a fair question with no answer here beyond the arithmetic -- his
arrangement is stated for his side and the transposition loses a little.

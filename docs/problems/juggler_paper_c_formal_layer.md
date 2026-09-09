# Juggler Paper C formal layer: three small formal attacks and a build root

Status: **PROMOTE** (three lemmas of Paper C moved from human proof to
kernel-checked Lean and the paper's table, Appendix A and Appendix B
updated in place; Paper C now has a barrel and an axiom artifact like
Papers A and B; nothing with analytic content was touched)

Not a new theorem about the map, not a density estimate, not a halt
theorem. The objects are Paper C
([juggler_fate_almost_all_note.md](../theory/juggler_fate_almost_all_note.md))
Lemma 4.1, Lemma 5.1 and Proposition 6.3(i), and the paper's own
verification table.

## Problem

How much of Paper C is Lean, and which of its human-proof statements are
small enough to formalize without inventing anything?

## Exact statement

Three statements, each now a Lean theorem with the paper's proof, and
(second pass, same day) Lemma 8.2 with the exact skeleton of Theorem 8.3.

**Lemma 4.1 (sweep; EXACT — LEAN VERIFIED, `FateSweep.lean`).** Let
\(x_0<\dots<x_{H-1}\) be reals with consecutive gaps in \([a,b]\),
\(0<a\le b\le\tfrac12\), \(b\le\tfrac{21}{20}a\) and \((H-1)a\ge 12\).
Then \(\#\{j:\{x_j\}<\tfrac12\}\ge H/7\) and
\(\#\{j:\{x_j\}\ge\tfrac12\}\ge H/7\); with the left-open half-cells,
i.e. the representative \(x-\lceil x\rceil+1\in(0,1]\), at least \(H/7\)
have representative \(\le\tfrac12\) and at least \(H/7\) have it
\(>\tfrac12\). Lean: `sweep_fract_lt_half`, `sweep_fract_ge_half`,
`sweep_rep_le_half`, `sweep_rep_gt_half`, all instances of
`Sweep.sweep_cell` (each residue of \(\lfloor 2x_j\rfloor\bmod 2\) holds
at least \(H/7\) terms).

**Lemma 5.1 (recursion; EXACT — LEAN VERIFIED, `FateRecursion.lean`).**
With \(e_i\in[e_{\min},e_{\max}]\subset(0,1)\), \(\lambda>0\),
\(\zeta=\sum_ic_ie_i^\lambda-1>0\), errors \(0\le\eta_i\le c_i\),
\(\sum_i\eta_i(t)e_i^\lambda\le\zeta/3\), \(\eta_0(t)\le\tfrac{2\zeta}3c_0\)
for \(t\ge t_1\), a seed \(g\ge c_0>0\) on \([e_{\min}t_1,t_1]\), and
\(g(t)\ge\sum_i(c_i-\eta_i(t))g(e_it)-\eta_0(t)\) for \(t\ge t_1\):
\(g(t)\ge c_0t_1^{-\lambda}t^\lambda\) for all \(t\ge e_{\min}t_1\).
Lean: `recursion_lemma`. The hypotheses \(\lambda<1\) and \(g\ge 0\) of
the paper are not needed.

**Proposition 6.3(i) (EXACT — LEAN VERIFIED, `FateFirstLetter.lean`).**
If some positive integer does not reach \(1\), the failure set has a
least positive member, and it is odd with an odd image. Lean:
`exists_minimal_failure`, `minimal_failure_odd_odd`, stated for any
forward-closed class excluding \(1\) (`minimalMember_odd`,
`minimalMember_image_odd`). The three first-letter pieces of Section
6.2 are `first_letter_trichotomy` and `first_letter_pieces_disjoint`.

**Lemma 8.2 and Theorem 8.3 (EXACT — LEAN VERIFIED, `FateChernoff.lean`).**
For \(C\ge 5\), \(d\ge CL\), \(d\ge 1\): at most \(2^d2^{-e(C)L}\) words
of length \(d\) are \(L\)-bad (`LBad_count_le`), by the Markov tilt of
`RateFreeDensity` on the constant weight at \(x=p_C/(1-p_C)\) and Gibbs'
inequality. With a floor \(N_0\ge 2\), the odd failures in \((y,2y]\)
lie in the cylinders of the envelope-bad words
(`oddFailures_subset_bad_cylinders`), which are \(L(y)\)-bad
(`LBad_of_envelopeBad`), so a bound \(M\) on every bad cylinder of depth
\(d\ge CL(y)\) gives \(\#\{	ext{odd failures}\}\le 2^d2^{-e(C)L(y)}M\)
(`oddFailures_card_le_chernoff`), and with \(d=\lceil CL(y)
ceil\) and
\(\mathrm H(C,A)\)'s bound on the \(O\)-rooted bad cylinders,
\(\#\{	ext{odd failures}\}\le y\Lambda^{-e(C)}+2\Lambda^Cy(\log y)^{-A}\)
at every \(y\ge 2\) (`oddFailures_card_le_explicit`), a factor \(2\)
against the paper's \(y/2\) and no \(arepsilon\). The absorption into
the displayed form and Corollary 8.4 stay human proofs.

**Theorem 9.2 (EXACT — LEAN VERIFIED, `FatePressure.lean`).** On the
live weight of `LiveCountWeight`: the live pressure is the generating
function of the live weight, a live start at depth \(d\ge CL(N)\) has
at least \(p_Cd\) odd letters (Lemma 8.1 on live starts), and a
pressure bound \(Na_	heta^dE\) at the tilt \(x=p_C/(1-p_C)\) gives at
most \(N\exp(-dD(p_C\|	frac12))E\) live starts
(`live_count_le_of_pressure`). The \(o(d)\) bookkeeping stays human.

**Lemma 5.2 (seed; EXACT — LEAN VERIFIED, `FateSeed.lean`).** A nonempty
backward-closed class contains some \(m\ge 3\)
(`exists_ge_three_of_backwardClosed`). For every \(y\ge(m+1)^4\), the
log-mass on \((\sqrt y,y]\) is at least the paper's
\(c_A=(1-2/m^4)(3/8\cdot 1/(m+1)-1/((m+1)^2-1))\) (`seed_lemma`,
`seed_constant_pos`).

**Theorem 7.2 (EXACT — LEAN VERIFIED given Theorem 5.3,
`FateTaoReduction.lean`).** A forward-closed class excluding \(1\)
whose odd members satisfy the rate \(y(\log y)^{-e}\) and whose
log-mass is at least \(K(\log x)^\lambda\) whenever nonempty, with
\(e>1-\lambda\), is empty of positive members
(`tao_rate_implies_empty`, `tao_rate_implies_conjecture` on the
failure set). The contagion bound itself stays a human proof.

**The build root (COMPUTATIONALLY VERIFIED).**
`formal/Problems/JugglerFatePaper.lean` imports exactly the eleven
modules Paper C cites; `formal/AxiomCheckPaperC.lean` prints the axioms
of the 135 cited declarations and `AxiomCheckPaperC.expected` records
them, every list a subset of `propext`, `Classical.choice`,
`Quot.sound`, no `sorryAx`, no `native_decide`.

## Current literature

- Paper C §1.4, Appendix A — `known`: the paper's own list of what is
  Lean. It was stale in one place: Proposition 9.3 was listed as a
  human proof after `TiltedShare.lean`
  ([failure margin](juggler_failure_margin.md)) proved it.
- Paper B's barrel `Problems.JugglerParityPaper` and
  `AxiomCheckPaperB` — `reproduced`: the same construction for Paper C.
- `Int.Ico_filter_modEq_card` (Mathlib) — `known`: the count of one
  residue class in an integer interval, used for the interior cells of
  one colour.

## Branch budget

```text
Mathematical target     Which human-proof statements of Paper C are
                        exact enough to be Lean, and are they.
Novelty hypothesis      None mathematical; the proofs are the paper's.
                        The laboratory gains a build root and an axiom
                        artifact for the third manuscript.
Falsifier               A proof that does not close in Lean without a
                        new idea, or a statement the Lean cannot cover
                        (then the row stays EXACT — HUMAN PROOF).
Already killed by?      none: no prior branch attempted these lemmas;
                        the ledger had no row for 4.1, 5.1 or 6.3(i).
Existing machinery      FateContagion.lean (closures, blocks, fibers),
                        floorPower_even_lt, floorPower_odd_even_two_step_lt,
                        RateFreeDensity / TiltedShare, formalpedia.
Maximum Phase-0 scope   Three modules, one barrel, one axiom artifact,
                        the paper's table and appendices. No analysis.
Promotion criterion     Not applicable: the statements are the paper's.
Stop criterion          All three compile without sorry, or one does not
                        and is recorded as deferred.
```

## Balanced-ternary formulation

None.

## Why BT may be relevant

Not relevant here; recorded for the template.

## Candidate operations / invariants

- The half-cell index \(\lfloor 2x\rfloor\): monotone along the
  sequence, rises by at most one per step when \(b\le\tfrac12\), even
  iff \(\{x\}<\tfrac12\) — **EXACT — LEAN VERIFIED** (`Sweep.cell_eq`,
  `Sweep.cell_succ_le`, `Sweep.cell_modEq_zero_iff`).
- The reflection \(x_j\mapsto -x_{H-1-j}\) carries closed half-cells to
  left-open ones and swaps nothing else — **EXACT — LEAN VERIFIED**
  (`sweep_ceil` from `Sweep.sweep_cell` with `Finset.sum_range_reflect`).
- Interior cells in place of traversed cells: at least \((T-3)/2\) of
  one colour against the paper's \(T_g\ge 10\); ratio \(11/25\) against
  \(10/23\); the final constant \(11/75>1/7\) is unchanged in kind —
  **EXACT — LEAN VERIFIED** (`Sweep.colour_cells_ge`, `Sweep.sweep_cell`).

## Experiments

- Probe: `research.juggler_sequence.paper_c_formal_layer` (reads the
  barrel, the artifact, Appendix A and the table; no computation on the
  map).
- Artifact: `data/research/juggler/paper_c_formal_layer/summary.json`.
- Tests: `tests/research/juggler_sequence/test_paper_c_formal_layer.py`,
  `tests/tools/test_formalpedia.py` (Paper C surface kernel-checked),
  `tests/research/juggler_sequence/test_layer_architecture.py`.
- Lean: `lake build Problems.JugglerFatePaper`;
  `lake env lean AxiomCheckPaperC.lean` reproduces the `.expected` file.

## Conjectures

None new.

## Counterexamples

None.

## Formalization

`formal/Problems/Juggler/FateSweep.lean` (26 declarations, namespace
`Sweep` for the cell machinery, five top-level theorems),
`formal/Problems/Juggler/FateSweepMonotone.lean` (Lemma 4.1'),
`formal/Problems/Juggler/FateRecursion.lean` (`recursion_lemma`),
`formal/Problems/Juggler/FateFirstLetter.lean` (7 declarations),
`formal/Problems/Juggler/FateChernoff.lean` (Lemma 8.2 and Theorem 8.3 in
explicit form, 31 declarations on `RateFreeDensity`'s word weights),
`formal/Problems/Juggler/FatePressure.lean` (Theorem 9.2 in exact form, 6
declarations on the live weight),
`formal/Problems/Juggler/FateTaoReduction.lean` (Theorem 7.2 given
contagion),
`formal/Problems/Juggler/FateSeed.lean` (Lemma 5.2),
`formal/Problems/JugglerFatePaper.lean` (barrel),
`formal/AxiomCheckPaperC.lean` and `.expected`. All kernel-checked; the
Paper C surface (root `Problems.JugglerFatePaper`, 42 modules reached,
1465 declarations) carries no `native_decide` and cites none.

Not formalized, and not claimed: Lemmas 4.2–4.3,
Proposition 4.4, the share law 4.5–4.6, Theorem 5.3, Theorem 7.3,
the asymptotic forms of Theorems 8.3 and 9.2, Corollary
8.4, Theorem 9.1, Section 10, Appendix C, and the log-mass bookkeeping
that turns the first-letter trichotomy into the identity (6.1).

## Results

Classification **PAPER_C_LEAN_SURFACE_CONSISTENT**.

```text
  Paper C verification table, before and after
  Lean rows      15 -> 16  (Lemma 4.1' on FateSweepMonotone)
  human rows     7 -> 7    (4.2--4.3 stay human; Theorems 5.3 and 7.3 stay human)
  cited names    135 -> 141, all on subsets of Mathlib's three axioms; none native_decide
```

- The three proofs are the paper's; the sweep count is the paper's
  with interior cells for traversed cells, which is one notion fewer
  and the same constant in kind.
- The recursion lemma holds under weaker hypotheses than printed:
  \(\lambda<1\) and \(g\ge 0\) are never used, and the extrema
  \(e_{\min},e_{\max}\) may be any bounds.
- The stale table line: Proposition 9.3 was Lean since
  `TiltedShare.lean` (row `J-tilted-share-telescoping`) and the paper
  still said human proof. Corrected in §1.4, §9.2 and Appendix A.

## Open questions

- Corollary 8.4 in Lean would need the contagion bound of Theorem 5.3,
  which is the analytic core; not a small attack.

## Decision

**PROMOTE.** Lemma 4.1' is now on the barrel with the rest of the
exact combinatorial layer. Nothing here changes a constant or an
exponent. Best next question: nothing on this branch; Theorem 5.3
stays human.

## Publication assessment

Status: `STRUCTURAL`. Paper C §1.4 and Appendix A updated in place; no
new manuscript sentence beyond the Lean citations.

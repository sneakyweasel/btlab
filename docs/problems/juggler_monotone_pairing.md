# Juggler monotone pairing: Lemma 4.1' of Paper C, its broken proof and the repair

Status: **PROMOTE** (the printed proof of Paper C Lemma 4.1' had two
false steps; the statement stands, with a corrected proof and the same
constant, now in the paper and in Lean)

Not a new estimate and not a change to any exponent. The object is one
lemma of Paper C
([juggler_fate_almost_all_note.md](../theory/juggler_fate_almost_all_note.md),
§4.1), found while preparing it for Lean
([Paper C formal layer](juggler_paper_c_formal_layer.md)).

## Problem

Is the printed proof of Lemma 4.1' (monotone pairing, scarcer colour
\(\ge H/3-2\)) correct, and if not, is the lemma?

## Exact statement

**Lemma 4.1' (EXACT — LEAN VERIFIED, corrected).** Let
\(x_1<\dots<x_H\) have consecutive differences in \([a,b]\),
\(0<a\le b\le\tfrac12\), \(b\le\tfrac{21}{20}a\), \((H-1)a\ge 12\), and
monotone (nondecreasing or nonincreasing). Then
\(\#\{j:\{x_j\}<\tfrac12\}\ge H/3-2\) and
\(\#\{j:\{x_j\}\ge\tfrac12\}\ge H/3-2\); the same for the left-open
cells \((k/2,(k+1)/2]\).

**The false step (REFUTED).** The proof printed until 8 September 2026
claimed that every pair of consecutive cells \((\rho,\rho')\) satisfies
\(\min\ge(\rho+\rho')/3\), because "the global drop of \(L=1/(2\delta)\)
is at most \(X/21\), spread over \(T^*\ge 22\) cells", and that for
\(X<2.1\) the pairs are \((1,1),(1,2),(2,2)\). Monotone steps need not
change gradually. Witness: \(a=\tfrac{10}{41}\) (\(X=2.05\)),
\(b=\tfrac{21}{82}=\tfrac{21}{20}a\), points
\(-2a,-a,0,a,2a,2a+b,2a+2b,\dots\): nondecreasing steps, cells
\([0,\tfrac12)\) and \([\tfrac12,1)\) hold \(3\) and \(1\) points, and
under the proof's pairing they are a pair. The proof also paired the
two partial end cells as if they were interior.

**The repair.** Fact (a): for interior cells \(i<j\),
\(\rho_j\le\rho_i+1\) (the \(\rho_i+1\) steps across cell \(i\) span
more than \(\tfrac12\), one exceeds \(1/(2(\rho_i+1))\), every step
inside cell \(j\) is at least that, and the \(\rho_j-1\) steps inside
cell \(j\) span less than \(\tfrac12\)). Pair the interior cells
consecutively, leave the first, the last and at most one interior cell
unpaired (\(\le 3G\) points), and write the scarcer count as
\(\ge(H-3G)/3+S\) with \(S=\sum_{\rm pairs}(\min-\mathrm{sum}/3)\); it
suffices that \(S\ge G-2\). Cases on \(G=\lfloor X\rfloor+1\) and
\(g=\lfloor 1/(2b)\rfloor\): \(G\ge7\) (ratio \(\ge 5/12\)),
\(3\le G\le 6\) with \(g\ge2\) (ratio \(\ge 3/8\), or the plateau
structure of (a) at \((4,2)\)), \(G=2\) (ratio \(\ge 1/3\)), and
\(G=3,g=1\) (after the first interior \(1\)-cell every cell holds
\(\le 2\); \((1,1)\) and six-point double pairs are impossible because
\(3b<1\) and \(7b<2\); every two consecutive pairs give \(\ge 3\) of
\(\le 8\)). All use \(H\ge 24X+1\ge 24G-23\). Full proof in the paper.

## Current literature

- Paper C Lemma 4.1' and Lemma 4.2 — `known`: Lemma 4.2 consumes the
  constant \(-2\) verbatim, so the repair had to keep it; it does.
- [OE-fiber constant](juggler_oe_fiber_constant.md) — `known`: the
  branch that introduced monotone pairing (\(1/7\to 1/3\)); its
  dossier records the "3+1 lock" remark, not the proof.
- Lemma 4.1 in Lean (`FateSweep.lean`, row `J-fate-sweep-lemma`) —
  `reproduced`: the cell machinery of the repair (occupancy bounds
  \(g\) and \(G\), the entry-within-\(b\) argument) is already formal.

## Branch budget

```text
Mathematical target     Whether Lemma 4.1' is true and proved.
Novelty hypothesis      None; a proof repair.
Falsifier               A monotone profile with a colour below H/3 - 2
                        (then the lemma, hence Lemma 4.2's 2/9 and the
                        pairing root 0.448, would fall).
Already killed by?      none: the OE-fiber-constant branch checked the
                        constant on fibers, not the proof's pair claim.
Existing machinery      FateSweep.lean; fate_contagion fiber census.
Maximum Phase-0 scope   One exact witness, one two-valued adversarial
                        search, one corrected proof. No Lean yet.
Promotion criterion     The corrected proof is complete and enters the
                        paper.
Stop criterion          A counterexample to the statement.
```

## Balanced-ternary formulation

None.

## Why BT may be relevant

Not relevant here; recorded for the template.

## Candidate operations / invariants

- Fact (a), later interior cells at most one fuller — **EXACT — HUMAN
  PROOF**; checked on every searched profile (`later_at_most_one_fuller`).
- The pair claim \(\min\ge\mathrm{sum}/3\) for every pair — **REFUTED**
  (witness above).
- The statement on two-valued monotone profiles — **COMPUTATIONALLY
  VERIFIED**, least slack \(1.33\) over \(H/3-2\).

## Experiments

- Probe: `research.juggler_sequence.monotone_pairing` (exact witness in
  `Fraction`; search over \(X\in[1,6)\), \(b/a\in\{1,1.02,1.04,1.05\}\),
  every switch point, \(64\) phases).
- Artifact: `data/research/juggler/monotone_pairing/summary.json`.
- Tests: `tests/research/juggler_sequence/test_monotone_pairing.py`.

## Conjectures

None new.

## Counterexamples

To the printed proof step, not to the lemma: \(a=10/41\), \(b=21/82\),
points \(-2a,-a,0,a,2a,2a+b,\dots\), pair \((3,1)\).

## Formalization

`formal/Problems/Juggler/FateSweepMonotone.lean` (row
`J-fate-monotone-pairing-repair`). Public theorems:
`sweep_monotone_cell`, `sweep_monotone_fract_lt_half`,
`sweep_monotone_fract_ge_half`, `sweep_monotone_ceil`,
`sweep_monotone_rep_le_half`, `sweep_monotone_rep_gt_half`. Fact (a)
is `fiber_card_le_succ` / `fiber_card_le_succ_anti`; the surplus cases
(c)–(f) and the \((4,2)\) straddle are in the same module. Left-open
cells are the closed case on \(j\mapsto -x_{H-1-j}\). No `sorry`.

## Results

Classification **PRINTED_PROOF_STEP_FALSE_STATEMENT_SUPPORTED**.

- The printed pair claim is false (exact witness); the lemma holds on
  \(4.2\cdot 10^6\) adversarial profiles at \(64\) phases each with slack \(\ge 1.33\).
- The corrected proof keeps the constant \(-2\), so Lemma 4.2, the
  pairing root \(0.448\), \(\lambda^{**}=0.4926\) and the Tao
  thresholds are unchanged.
- The erratum is in the paper, after the corrected proof.

## Open questions

- Whether the true constant is \(H/3-1\) (the search never goes below
  \(H/3-0.67\)); no consumer needs it. Not a Lean target.

## Decision

**PROMOTE.** The lemma survives, its proof is corrected, and the
English is covered by `FateSweepMonotone.lean`. Best next question:
nothing on this branch; Lemmas 4.2–4.3 stay human.

## Publication assessment

Status: `THEOREM`. Paper C §4.1: corrected proof and erratum remark in
place; no other sentence of the paper changes.

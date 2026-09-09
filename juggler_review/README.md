> **Offset-anchor research supplement, 9 September 2026:** [Nonzero-offset estimate](paper_b_offset_anchor_report.md) gives exponent 23/24, up to epsilon, for the stated zero-total-Y family with signed widened waves and already-differenced D2 factors. The corrected composite coefficient is 81/64. Full kernel assembly and OOOEE remain unproved; the 27/32 manuscript and deposit package are unchanged.

> **Wave-bearing research supplement, 9 September 2026:** [Widened D1 repair](paper_b_wave_bearing_report.md) gives exponent 31/32, up to epsilon, for the nonzero-total-Y family with the stated D2 factors and partition conditions. The nonzero-offset family at zero total Y frequency, complete kernel, and OOOEE remain unproved. The 27/32 manuscript and deposit package are unchanged.

> **Signed-wave research supplement, 9 September 2026:** [Combined zero-offset estimate](paper_b_signed_waves_report.md) proves the specified signed family with exponent 31/32, up to epsilon, including the D2 factors. Full kernel assembly and OOOEE remain unproved. The 27/32 manuscript and deposit package are unchanged.

> **D2 research supplement, 9 September 2026:** [D2 repair and signed-wave obstruction](paper_b_d2_report.md) records a new fixed-label reduction. The kernel and OOOEE count remain unproved; the 27/32 manuscript and deposit package are unchanged.

> **Paper B OOEOE repair, 9 September 2026:** the current preprint proves four-step certificate density 13/16 and a five-step certificate subfamily of density 27/32. Full five-step density 7/8 now requires only OOOEE. The general decorated kernel remains unproved. See [the current report](paper_b_ooeoe_report.md) and [build instructions](../docs/theory/PAPER_B_BUILD.md). Earlier theorem numbers and companion cross-citations require review.

# Juggler reviewer bundle (three manuscripts)

Author: Philippe Cochin. Review-repair snapshot: 9 September 2026.

**Later 9 September source correction:** the canonical Paper C now
restricts H to bad words and H_q to bad prefixes. The unrestricted
versions are refuted by the exact
[absorbed-cylinder proof](../docs/problems/juggler_absorbed_cylinder.md).
This snapshot's Paper C Markdown and PDF predate that correction and
must be rebuilt from `docs/theory/` before further external review.
The stopped live-pressure hypothesis is unchanged and unproved.

Status: Paper A is the regenerated Zenodo preprint of 9 September 2026; Paper B is the repaired
preprint (four-step certificate density 13/16, five-step subfamily density
27/32, and conditional full five-step density 7/8); Paper C
(fate contagion and the almost-all reformulation, 4 September 2026)
is a complete draft whose main theorem is unconditional and whose
Appendix C alone depends on Paper B.

This folder is a snapshot of the files to send for external review. It
is not the laboratory. No unconditional termination theorem is claimed.

The 9 September repair corrects six reviewed claim-level issues: general
floor fibers, cycle-run scope, the new kernel application's interval scale,
biased pressure rates and their hypotheses, the charge obstruction's
anchor assumption, and the extended window's formal coverage and endpoint.
The exact integer core and existing conditional reductions are retained;
unproved extensions are not promoted by these corrections.

**Source of truth is `docs/theory/`.** Edit
[juggler_finite_dynamics_note.md](../docs/theory/juggler_finite_dynamics_note.md),
[juggler_parity_discrepancy_note.md](../docs/theory/juggler_parity_discrepancy_note.md)
and
[juggler_fate_almost_all_note.md](../docs/theory/juggler_fate_almost_all_note.md)
there, then rebuild this bundle. Do not hand-edit both copies.

Interactive glossary and playground (Paper A vocabulary only):
https://sneakyweasel.github.io/btlab/

## Read this first

1. [juggler_finite_dynamics_note.pdf](juggler_finite_dynamics_note.pdf)
   is the current **Paper A** preprint
   ([doi:10.5281/zenodo.22676453](https://doi.org/10.5281/zenodo.22676453),
   [Zenodo](https://zenodo.org/records/22676453)). It includes the corrected rotation
   cells, full finite-window estimate, exact threshold table, updated Lean
   uniqueness result, scoped companion context, and explicit AI disclosure.
   Theorem 3.31 gives the computational eight-even-step exclusion.
   The finite-window charge theorem covers \([50508,16785921)\).
   Its strongest reported period floor remains 780239 at the supplied
   descent floor 350000000. The formalization map and reviewer packet are
   generated copies of their canonical `docs/theory/` inputs.
   Rebuild with `python tools/build_paper_a.py`; verify every copy with
   `python tools/build_paper_a.py --check`. See
   [build instructions](../docs/theory/PAPER_A_BUILD.md).
2. [juggler_parity_discrepancy_note.pdf](juggler_parity_discrepancy_note.pdf)
   — **Paper B**: *Parity Statistics of Nested Floor Powers: Finite-Step
   Descent and Conditional Extensions for the Juggler Map* (9 September 2026).
   Theorem 4.5 proves restricted mixed exponential sums by an exact carry
   expansion and estimates over every gap cell. Corollary 4.6 and Theorem
   5.2 give the unconditional four-step power-envelope certificate density
   \(13/16\), with error \(O(N^{23/24}(\log(2N))^3)\). Proposition 3.2
   repairs the OE count, and Proposition 7.6 treats a basic collision model.
   Corollary 4.10 proves the OOEOE split with error \(O(N^{47/48})\).
   Theorem 5.3 gives a five-step certificate subfamily of density \(27/32\);
   Theorem 5.4's full five-step density \(7/8\) requires only OOOEE.
   The general decorated kernel, short-interval extension, complete
   depth-four census, and density-one conclusion remain unproved or
   conditional as stated in the paper. These are written analytic arguments;
   no new Lean formalization or independent peer review is claimed.
   See [the current report](paper_b_ooeoe_report.md). The
   [historical audit ledger](paper_b_audit_ledger.md) concerns the superseded
   4 September draft and does not validate the current analytic proofs.
3. [juggler_fate_almost_all_note.pdf](juggler_fate_almost_all_note.pdf)
   — **Paper C**
   ([doi:10.5281/zenodo.22678165](https://doi.org/10.5281/zenodo.22678165),
   [Zenodo](https://zenodo.org/records/22678165)):
   *Fate Contagion in the Juggler Map and the
   Almost-All Reduction of Termination* (4 September 2026; first
   complete draft 3 September, revised the same day after a first
   external review; pairing and consistency pass 4 September).
   Theorem 1: every nonempty backward-closed set (every realized fate
   class: reaching \(1\), a cycle basin, divergence) has
   \(\sum_{n\le x}1/n\gg(\log x)^{\lambda}\) for
   \(\lambda<\lambda^{**}=0.4926\) (elementary: even blocks are
   intervals, \(OE\) fibers have monotone pairing \(H_m/3-2\);
   abstract recursion lemma). Theorem 2: odd generation (Lean).
   Theorem 3: the conjecture is equivalent to a Tao-type almost-all
   bound with bounded target and rate \((\log y)^{-e}\),
   \(e>0.5074\). Theorem 4:
   that bound follows from parity control on itinerary cylinders of
   depth \(C\log_2\log y\), in a hierarchy of forms down to a single
   exponential moment of the odd count on live starts (\(C\ge19\)
   for the fair optimized-tilt hypothesis; biased forms have
   \(q\)-dependent rates and depths). These hypotheses remain unproved.
   Theorem 5: the exact first-letter decomposition
   has one free term, the infinite-depth live mass; \(S\)-fairness is
   defined and the walk argument labelled a heuristic; a narrowly
   stated depth-uniformity budget. Appendix C (exponent \(0.5392\),
   \(C\ge 18\)) is conditional on the standalone Hypothesis L, the
   only import from Paper B (now its Theorem 4.12, Section 3.5, still
   an unrefereed working draft), with the downstream derivations
   written out. Proposition 4.4 now carries the explicit constant
   \(C_0=250\). Three figures (dependency map, productions,
   decomposition). Lean exact layer; one numerical section, labelled
   observation. Excludes no fate.
4. [juggler_finite_dynamics_reviewer_packet.md](juggler_finite_dynamics_reviewer_packet.md)
   — claim map and falsifiers for the three papers. Optional for the
   proofs.

Markdown sources:
[juggler_finite_dynamics_note.md](juggler_finite_dynamics_note.md),
[juggler_parity_discrepancy_note.md](juggler_parity_discrepancy_note.md)
and [juggler_fate_almost_all_note.md](juggler_fate_almost_all_note.md).
The historical Paper B frontier figure is
[figures/juggler_frontier.png](figures/juggler_frontier.png).

## Optional Lean map

- [juggler_finite_dynamics_formalization.md](juggler_finite_dynamics_formalization.md)
  — theorem names. The Lean import graph is
  [figures/juggler_lean_layers.png](figures/juggler_lean_layers.png).

The paper barrel depends on the repository's full Lean source tree and is
therefore not duplicated in this snapshot. To check the Lean proofs, clone
the repository and from `formal/` run

```text
lake build Problems.JugglerPaper
```

Paper A Zenodo record
[doi:10.5281/zenodo.22676453](https://doi.org/10.5281/zenodo.22676453)
and deposit kit: [zenodo_paper_a/](zenodo_paper_a/).
Paper B prepared deposit kit (no record yet):
[zenodo_paper_b/](zenodo_paper_b/).
Paper C Zenodo record
[doi:10.5281/zenodo.22678165](https://doi.org/10.5281/zenodo.22678165)
and deposit kit: [zenodo_paper_c/](zenodo_paper_c/).

Repository: https://github.com/sneakyweasel/btlab/

The core mathematical lemmas of Paper A are mechanized in Lean 4;
selected finite classifications and the descent floor are
independently certified computations. Theorems 4.6 and 4.8 are
verified computations. Proposition 4.9's arithmetic is Lean.
The repaired analytic estimates of Paper B are written proofs and are
not in Lean. The general kernel theorem remains unproved. Only selected
exact floor reductions from the earlier draft are formalized
(`GapCells.lean`, including the double-gap identity
`seq_floor_gap_second`). Paper C's exact layer (closure of the fate
classes, trichotomy and exclusion, the even block and \(OE\) fiber
as intervals, odd generation, envelope descent into the floor) is
Lean (`FateContagion.lean`). The seed and abstract recursion are also
formalized. `tao_rate_implies_conjecture` is a compiled conditional
theorem assuming the contagion lower bound and the Tao-rate upper bound;
it does not establish those hypotheses. The production estimates and
asymptotic counting remain human-proof objects; censuses are observations.

## What is not here

The full `Problems.Juggler` laboratory stack, the Word Atlas, pytest
records, and internal dossiers. Those are not required to read either
paper.

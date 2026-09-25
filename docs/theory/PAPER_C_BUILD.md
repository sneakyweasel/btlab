# Paper C — reproducible preprint build

The canonical manuscript is [juggler_fate_almost_all_note.md](juggler_fate_almost_all_note.md). The 9 September 2026 revision was the first Zenodo preprint, [doi:10.5281/zenodo.22678165](https://doi.org/10.5281/zenodo.22678165); the current deposit is version 1.3.0 of 24 September 2026, [doi:10.5281/zenodo.22947659](https://doi.org/10.5281/zenodo.22947659), listed with the others under Zenodo below. A local rebuild does not create or update that record.

The local 11 September 2026 rebuild refreshes source hashes after a shared Lean refactor and repairs Unicode text encoding in the PDF template. It preserves the mathematical text, title and date; it does not update the deposited version.

The local 21 September 2026 revision adds Section 5.8, the two-production route to Theorem 1 through the poor-fiber tail, with five further Lean modules (FateBlockLock, FateFiberLock, FateResonanceCount, FatePoorTail, FatePoorProduction) wired into the barrel and the axiom artifact. Theorem 1 is stated for every lambda below lambda_ideal, about 0.4927, and is machine-checked with no hypothesis for lambda at most 100/203, above the deposited lambda** of about 0.4926; Theorems 3 and 4 and the closing target use the threshold 1 - lambda_ideal, machine-checked as 103/203, with the depth constants unchanged. Sections 5.7, 6.3 and 7.1 gain the Collatz identity behind the ideal coefficient, the exponent bridge to Paper B and the counterexample {3 * 2^k} to the Collatz analogue of Theorem 1; Section 5.6 records that the depth-two gap is closed; the companion references carry their Zenodo DOIs and current titles; the date moves to 21 September. The same day's closure adds a thirty-seventh module, FateDyadicDensity: Corollary 5.4, the dyadic pigeonhole, and Corollary 5.5 at the three fate classes are Lean at 100/203, so every clause of Theorem 1 is formalized at that exponent and the human remainder of Theorem 1 is the range 100/203 < lambda < lambda_ideal. Between the deposit and this revision the intermediate rebuilds of 13 to 20 September had already raised the unconditional exponent of the pointwise route from 3/10 to 13/40, lowered the hypothesis-free rate threshold from 7/10 to 27/40, named the thirty-first module and added the Corollary 5.4/5.5 rows. None of this updates the deposited version.

## Build and provenance

The local 22 September 2026 correction qualifies Section 5.7's second
moment identity: completeness of a prefix-free family is insufficient
at an unbounded stopping time. All minimal descent certificates have
fair mass one but multiplier moment at most 3/4. The coefficient shift,
Proposition 5.12, and all termination thresholds are unchanged.
`Problems/Juggler/CollatzMoments.lean` checks the coefficient shift,
fixed-depth identities, and the counterexample. This auxiliary bridge
module has its own dependency audit; it is not added to the Paper C
theorem barrel. The local correction does not update a deposited version.

From the repository root, with Pandoc and XeLaTeX installed:

```text
python tools/build_paper.py C            # PDF, LaTeX, metadata, manifest and kit
python tools/build_paper.py C --check    # release and kit against the manifest
python tools/build_paper.py C --sync     # regenerate the kit from a current release
```

Every paper uses this one builder; the settings particular to Paper C (its files,
Lean roots, Zenodo fields and LaTeX options) are in `tools/papers/c.json`.

The build compiles three passes, rejects overfull boxes, missing glyphs and unresolved references, and then synchronizes the canonical PDF in `preprints/` and its Zenodo PDF alias. It writes a hash manifest and prepared Zenodo metadata. It does not publish a website or upload a deposit. The generated LaTeX can also be compiled directly beside the `figures` directory. `--sync` only copies a build whose input and output hashes still match. Figure regeneration requires matplotlib and is run with `python docs/theory/figures/render_paper_c_figures.py` before rebuilding.

## Verification and scope

In `formal`, using its pinned Lean toolchain and Lake manifest, run `lake build Problems.JugglerFatePaper` and `lake env lean AxiomCheckPaperC.lean`. Save the latter's output, then from the repository root run:

```text
python tools/check_paper_c_numeric.py --axiom-output path/to/AxiomCheckPaperC.actual
```

The arithmetic check requires mpmath. It recomputes the finite-production roots and depth constants at 90 decimal digits, checks exact nested landing endpoints and finite word counts, and checks the printed formal interface against the supplied fresh axiom output. The 21 September 2026 review built the Paper C target and matched all 473 printed axiom reports. Only `propext`, `Classical.choice` and `Quot.sound` occur in those reports, and two declarations rest on no axiom at all.

These checks do not formalize the analytic proofs. In particular, Proposition 4.4, the share-law estimate, production assembly in Appendix D and the limiting analytic arguments remain mathematical prose; since the 21 September revision they are the first route to Theorem 1 and no longer on its critical path, the second route being formalized end to end. The hypotheses for a time-bounded almost-all result and Appendix C's Hypothesis L remain open. No assertion excludes every nontrivial cycle or unbounded orbit.

## Corrections in this version

The eventual-entry equivalence is separated from sufficient stopping-time estimates. The unsupported numerical block constant 250 is replaced by an absolute unspecified constant. The share-law error includes phase tangencies, and the finite nested productions receive a self-contained proof with their exact endpoints. The free-term normalization and the slack exponent in the upper recursion are corrected. The tower comparison is limited to its reference model. The numerical section uses archived depths and excludes the capped pressure run from the quoted comparison. Decimal root displays are rounded; defining equations govern strict thresholds.

Development notes are historical. Where their statements differ, the corrected manuscript governs this release. Archived JSON retains the original parameters; running current code can report newer rate constants. The large archived experiments were inspected, not all rerun during this review. The existing 350,000,000 descent certificate is inherited from Paper A; no new floor campaign was performed.

## Zenodo

This repository holds version 1.3.0, deposited on 24 September 2026 as [doi:10.5281/zenodo.22947659](https://doi.org/10.5281/zenodo.22947659), record [zenodo.org/records/22947659](https://zenodo.org/records/22947659). The record's one file is byte-identical to the repository PDF by the md5 the Zenodo API reports. Earlier versions are 1.1.0, [doi:10.5281/zenodo.22865705](https://doi.org/10.5281/zenodo.22865705), of 21 September 2026, and 1.0.0, [doi:10.5281/zenodo.22678165](https://doi.org/10.5281/zenodo.22678165), of 9 September 2026. The concept DOI [10.5281/zenodo.22678164](https://doi.org/10.5281/zenodo.22678164) resolves to the latest version. Resource type Publication / Preprint, English, open access, CC BY 4.0, with the author's ORCID [0009-0004-1939-3382](https://orcid.org/0009-0004-1939-3382). A rebuild writes local metadata only; it does not upload a new version. Later revisions should use that record's new-version operation. The manuscript includes an AI-assistance disclosure and the author's responsibility statement.

## Revision of 22 September 2026: three productions

Version 1.2.0 incorporates the complete written OOEE poor-fiber argument
as Appendix E and its physical-cutoff assembly as Theorem 5.19. Theorem 1
now reaches 5/8; Theorems 3 and 7.2--7.3 use the sufficient rate e > 3/8.
The earlier two-production exponent 100/203 remains the fully kernel-checked
baseline. The new analytic proof is AI-assisted and awaits independent
review and complete Lean verification. Theorem 9.4 adds the scale-average
pressure implication, separately Lean at r - eta > 103/203 and written
at r - eta > 3/8 using the new contagion theorem. The refactored Lean
reduction now also proves the latter implication conditional on
OOEEProductionBound; its supplementary audit selects fourteen declarations.

The historical 37-module barrel and its 473 reports are unchanged. The
supplementary OOEE assembly, weighted OE, mixed-mode and scale-average
modules retain separate audits. Their transitive sources and the written
proof notes are included in the release provenance. A conditional Lean
assembly does not certify the complete analytic input. Earlier numerical
depth tables remain labelled comparisons at their original thresholds.
The dependency diagram and metadata now describe this edition.

## Revision of 24 September 2026: five productions

Version 1.3.0 adds Section 5.10. Theorem 5.20 feeds the two five-letter
words OOOEE and OOEOE into the recursion through Theorem 6.3 of Paper B
(version 1.2.0, doi:10.5281/zenodo.22946276), and raises Theorem 1 to
37/50 and lowers the sufficient rate threshold of Theorems 3, 7.2--7.3
and 9.4 to 13/50. Paper B's Theorem 6.3 is an AI-assisted written proof that has
not been independently reviewed. The deduction from it
(FateDepthFiveWeighted, with the fibre geometry of DepthFiveFibreGeometry)
and the five-production recursion (FateDepthFiveAssembly) are
kernel-checked.

The same revision records that the log-mass bound of Theorem 5.19 is now
kernel-checked. FateOOEEWeighted proves the actual OOEE production from a
count form of the poor-fiber tail (OOEEResonanceTail), so contagion 5/8
and the threshold 3/8 hold in Lean with no contagion-side hypothesis; the
dyadic clause of Theorem 1 and Corollary 7.1 remain written. The least depth constants
are recomputed for both thresholds in Appendix B. Arb certifies each
value and the failure of the integer below it, and
`check_paper_c_numeric.py` recomputes them at 90 digits; the historical
lambda** constants remain as comparisons. Appendix B limits "closed" to
the localized route of the depth-five words and corrects that model's
root to 0.6066; the value 0.5561 printed before matched no recursion of
its form. The dependency figure is redrawn, reference [12] cites Paper B
1.2.0, and the citations of numbered results from an earlier Paper B
draft are replaced by the results Paper B 1.2.0 contains. A three-lens
AI review of this revision found no mathematical error in Section 5.10;
its findings on status wording and stale sentences are repaired. The historical 37-module barrel and
its 473 reports are unchanged; the supplementary modules and their audits
are pinned in the release manifest. This version was deposited on 24
September 2026 as doi:10.5281/zenodo.22947659.

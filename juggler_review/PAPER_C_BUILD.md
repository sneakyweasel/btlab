# Paper C — reproducible preprint build

The canonical manuscript is [juggler_fate_almost_all_note.md](juggler_fate_almost_all_note.md). The 9 September 2026 revision is the Zenodo preprint [doi:10.5281/zenodo.22678165](https://doi.org/10.5281/zenodo.22678165). A local rebuild does not create or update that record.

## Build and provenance

From the repository root, with Pandoc and XeLaTeX installed:

```text
python tools/build_paper_c.py
python tools/build_paper_c.py --check
```

The build compiles three passes, rejects overfull boxes, missing glyphs and unresolved references, and then synchronizes the canonical PDF, review copies, figures and local companion PDF. It writes a hash manifest and prepared Zenodo metadata. It does not publish a website or upload a deposit. The generated LaTeX can also be compiled directly beside the `figures` directory. `--sync` only copies a build whose input and output hashes still match. Figure regeneration requires matplotlib and is run with `python docs/theory/figures/render_paper_c_figures.py` before rebuilding.

## Verification and scope

In `formal`, using its pinned Lean toolchain and Lake manifest, run `lake build Problems.JugglerFatePaper` and `lake env lean AxiomCheckPaperC.lean`. Save the latter's output, then from the repository root run:

```text
python tools/check_paper_c_numeric.py --axiom-output path/to/AxiomCheckPaperC.actual
```

The arithmetic check requires mpmath. It recomputes the finite-production roots and depth constants at 90 decimal digits, checks exact nested landing endpoints and finite word counts, and checks the printed formal interface against the supplied fresh axiom output. The release review built the Paper C target and matched all 141 printed axiom reports. Only `propext`, `Classical.choice` and `Quot.sound` occur in those reports.

These checks do not formalize the analytic proofs. In particular, Proposition 4.4, the share-law estimate, production assembly in Appendix D and the limiting analytic arguments remain mathematical prose. The hypotheses for a time-bounded almost-all result and Appendix C's Hypothesis L remain open. No assertion excludes every nontrivial cycle or unbounded orbit.

## Corrections in this version

The eventual-entry equivalence is separated from sufficient stopping-time estimates. The unsupported numerical block constant 250 is replaced by an absolute unspecified constant. The share-law error includes phase tangencies, and the finite nested productions receive a self-contained proof with their exact endpoints. The free-term normalization and the slack exponent in the upper recursion are corrected. The tower comparison is limited to its reference model. The numerical section uses archived depths and excludes the capped pressure run from the quoted comparison. Decimal root displays are rounded; defining equations govern strict thresholds.

Development notes are historical. Where their statements differ, the corrected manuscript governs this release. Archived JSON retains the original parameters; running current code can report newer rate constants. The large archived experiments were inspected, not all rerun during this review. The existing 350,000,000 descent certificate is inherited from Paper A; no new floor campaign was performed.

## Zenodo

The published record is [doi:10.5281/zenodo.22678165](https://doi.org/10.5281/zenodo.22678165) ([Zenodo](https://zenodo.org/records/22678165)), version 1.0.0, 9 September 2026. Resource type Publication / Preprint, English, open access, CC BY 4.0. A rebuild writes local metadata only; it does not upload a new version. Later revisions should use that record's new-version operation. The manuscript includes an AI-assistance disclosure and the author's responsibility statement.

# Paper B: conditional preprint release

Version: 2026-09-09-conditional. Author: Philippe Cochin.

The publication is **Parity Statistics of Nested Floor Powers: Conditional Descent Results for the Juggler Map**. The PDF has nine pages. Its unconditional certificate-density result is 3/4; the 13/16, 7/8, and density-one conclusions require the hypotheses printed in the paper. The package does not certify the earlier deterministic kernel estimates.

## Files for Zenodo

Upload `juggler_parity_discrepancy_note.pdf` and `paper_b_source_package.zip`. The latter contains the manuscript sources, build assets, exact validation script and results, and this guide. `paper_b_zenodo_fields.txt` and `paper_b_zenodo.json` provide prepared record fields. They are local preparation materials, not an existing deposit. Set the actual first-publication date in Zenodo. No DOI has been reserved or inserted.

`paper_b_review.md` explains the original proof gaps and the scope of the replacement. The old 4 September working draft is preserved separately in the repository as `juggler_parity_discrepancy_note_2026_09_04.md`; it is not the publication source. Earlier theorem numbering is superseded.

## Rebuild from the standalone source package

Requirements: Python 3.10 or newer, Pandoc, and XeLaTeX with the standard AMS, geometry, longtable, booktabs, array, calc, needspace, xurl, and hyperref packages. The validated build used Pandoc 3.6.3 and MiKTeX-XeTeX 4.18 (MiKTeX 26.5).

Extract the source ZIP into a new directory and run there:

```text
python build_paper_b.py
python validate_paper_b.py --output paper_b_validation.json
```

The build reads the Markdown and `build/article.tex` / `build/layout.lua`, compiles twice, and writes the PDF, generated LaTeX, and `paper_b_build.json`. It stops on overfull boxes, missing glyphs, or undefined references. Use `--pandoc` and `--xelatex` with executable paths if they are not on PATH. Use `--output-dir` and `--build-dir` to choose output locations. The supplied LaTeX can also be compiled directly with XeLaTeX twice.

From the laboratory repository root, the corresponding commands are:

```text
python tools/build_paper_b.py
python tools/validate_paper_b.py --output docs/theory/paper_b_validation.json
```

The repository builder uses `docs/theory/` as the source directory and `tools/paper_b/` for its assets. Review the PDF after every changed build; rebuilds can differ at the byte level because PDF metadata includes build information. `paper_b_build.json` records hashes of the actual delivered build, and `SHA256SUMS.txt` records the package files.

After a repository rebuild, synchronize the Markdown and PDF copies in `juggler_review/` and the PDF in `web/juggler-companion/public/papers/`. The build command itself writes only its selected output directory. Run the repository's manuscript-mirror and documentation-link checks before preparing another release. The copies delivered by this review are synchronized.

## Validation scope

The standalone script uses only Python's standard library and exact integer or rational arithmetic. It checks 16,000 power envelopes, 6,231 branch indicators, 3,150 algebraic identities and bounds, and 10,201 carry identities. It enumerates the minimal contracting words through depth five and auxiliary word counts through depth sixteen. Its density fractions are conditional fair-share sums, not measurements or proofs of asymptotic orbit densities.

The manuscript's analytic and conditional arguments are written proofs. Neither this script nor the older repository audits provide independent validation of the unresolved nested correlations. No complete Lean verification is claimed for this revision.

## Prepared licensing

The proposed manuscript and release-documentation license is Creative Commons Attribution 4.0 International, matching the prepared Zenodo fields: <https://creativecommons.org/licenses/by/4.0/>. This is an editable deposit choice. The Python and Lua build/validation code follows the repository's MIT license, included as `LICENSE-MIT.txt` in the source package. Third-party tools and cited works retain their own licenses.

## Publication status

This is a locally prepared conditional preprint. It has not been uploaded or published by this review. Author approval of the final text and record fields remains part of the publication decision. Companion manuscripts that use the former unconditional Paper B claims need a separate dependency review.

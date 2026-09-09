# Paper B: OOEOE repair release

Version: 2026-09-09-ooeoe-repair. Author: Philippe Cochin.

The publication is **Parity Statistics of Nested Floor Powers: Finite-Step Descent and Conditional Extensions for the Juggler Map**. The PDF has seventeen pages. The four-step power-envelope certificate density 13/16 is unconditional, with error O(N^(23/24) log(2N)^3). The OOEOE count adds a disjoint five-step certificate subfamily, giving density 27/32 with error O(N^(47/48)). The full five-step density 7/8 requires only the remaining OOOEE correlation hypothesis; density-one certificates require fixed-depth equidistribution. The general decorated kernel and short-interval estimates remain unproved.

## Files for Zenodo

Upload `juggler_parity_discrepancy_note.pdf` and `paper_b_source_package.zip`. The latter contains the manuscript sources, build assets, exact validation script and results, and this guide. `paper_b_zenodo_fields.txt` and `paper_b_zenodo.json` provide prepared record fields. The reviewer kit `juggler_review/zenodo_paper_b/` holds the deposit-named PDF alias `Parity_Statistics_of_Nested_Floor_Powers.pdf` and generated `ZENODO_FIELDS.txt`. They are local preparation materials, not an existing deposit. Set the actual first-publication date in Zenodo. No DOI has been reserved or inserted.

`paper_b_review.md` records the initial review and original proof gaps. The first repair report, paper_b_repair_report.md, records the four-step repair. The current paper_b_ooeoe_report.md records its audit, the OOEOE proof, the 27/32 subfamily, and the bounded kernel assessment. The old 4 September working draft is preserved separately in the repository as `juggler_parity_discrepancy_note_2026_09_04.md`; it is not the publication source. Earlier theorem numbering is superseded.

## Rebuild from the standalone source package

Requirements: Python 3.10 or newer, Pandoc, and XeLaTeX with the standard AMS, geometry, longtable, booktabs, array, calc, needspace, xurl, and hyperref packages. The validated build used Pandoc 3.6.3 and MiKTeX-XeTeX 4.18 (MiKTeX 26.5).

Extract the source ZIP into a new directory and run there:

```text
python build_paper_b.py
python validate_paper_b.py --output paper_b_validation.json
python validate_paper_b_repairs.py --output paper_b_repair_validation.json
python validate_paper_b_ooeoe.py --output paper_b_ooeoe_validation.json
```

The build reads the Markdown and `build/article.tex` / `build/layout.lua`, compiles twice, and writes the PDF, generated LaTeX, and `paper_b_build.json`. It stops on overfull boxes, missing glyphs, or undefined references. Use `--pandoc` and `--xelatex` with executable paths if they are not on PATH. Use `--output-dir` and `--build-dir` to choose output locations. The supplied LaTeX can also be compiled directly with XeLaTeX twice.

From the laboratory repository root, the corresponding commands are:

```text
python tools/build_paper_b.py
python tools/validate_paper_b.py --output docs/theory/paper_b_validation.json
python tools/validate_paper_b_repairs.py --output docs/theory/paper_b_repair_validation.json
python tools/validate_paper_b_ooeoe.py --output docs/theory/paper_b_ooeoe_validation.json
```

The repository builder uses `docs/theory/` as the source directory and `tools/paper_b/` for its assets. Review the PDF after every changed build; rebuilds can differ at the byte level because PDF metadata includes build information. `paper_b_build.json` records hashes of the actual delivered build, and `SHA256SUMS.txt` records the package files.

A repository rebuild that writes to `docs/theory/` also synchronizes the Markdown and PDF copies in `juggler_review/`, the companion PDF, and `juggler_review/zenodo_paper_b/`. Use `python tools/build_paper_b.py --sync` to repair those exports without recompiling, and `--check` to verify them. A standalone package build still writes only its selected output directory. Run the repository's manuscript-mirror and documentation-link checks before preparing another release.

## Validation scope

The standalone script uses only Python's standard library and exact integer or rational arithmetic. It checks 16,000 power envelopes, 6,231 branch indicators, 3,150 algebraic identities and bounds, and 10,201 carry identities. It enumerates the minimal contracting words through depth five and auxiliary word counts through depth sixteen. Its density fractions are finite word-weight sums, not measurements or proofs of asymptotic orbit densities. The new repair validator additionally passes 1,920 differenced-identity checks, 2,000 carry-expansion checks, and 40 exponent comparisons. The OOEOE validator checks 1,275 exact centering identities, the frozen-frequency curvature coefficient, five squared-sum exponents, ten strict exponent comparisons, and the certificate fractions.

The manuscript's analytic and conditional arguments are written proofs. The exact scripts support algebra and exponent bookkeeping; neither they nor the older repository audits prove asymptotic cancellation or independently validate the new arguments. No complete Lean verification is claimed for this revision.

## Prepared licensing

The proposed manuscript and release-documentation license is Creative Commons Attribution 4.0 International, matching the prepared Zenodo fields: <https://creativecommons.org/licenses/by/4.0/>. This is an editable deposit choice. The Python and Lua build/validation code follows the repository's MIT license, included as `LICENSE-MIT.txt` in the source package. Third-party tools and cited works retain their own licenses.

## Publication status

This is a locally prepared preprint with proved four-step and OOEOE results and conditional extensions. It has not been uploaded or published by this review. Author approval of the final text and record fields remains part of the publication decision. Companion manuscripts that use the former unconditional Paper B claims need a separate dependency review.

# Paper B: consolidated five-step preprint

Version: 2026-09-10-proof-audit. Author: Philippe Cochin.

The 37-page manuscript proves full five-step power-envelope certificate
density 7/8, with count error O_epsilon(N^(127/128+epsilon)).
Theorem 4.11 and Appendices A-C contain the complete OOOEE proof;
Theorem 5.4 gives the count. The four-step density 13/16 and OOEOE
estimate remain included. The stronger historical 95/96 target,
arbitrary decorations, localization, and all-depth hypotheses remain open.

## Deposit files

Upload juggler_parity_discrepancy_note.pdf and paper_b_source_package.zip.
The source ZIP contains the complete manuscript, generated LaTeX,
build assets, all exact-control scripts, aggregate validation, fresh proof audit, metadata, and this guide. paper_b_zenodo_package.zip collects
the prepared deposit materials for convenience.

Prepared fields: paper_b_zenodo.json and paper_b_zenodo_fields.txt.
The repository reviewer kit also contains the byte-identical PDF alias
Parity_Statistics_of_Nested_Floor_Powers.pdf and generated ZENODO_FIELDS.txt.
No deposit or DOI has been created. Use the actual first-publication date.

## Standalone rebuild

Requirements: Python 3.10+, Pandoc, and XeLaTeX with AMS, geometry,
longtable, booktabs, array, calc, needspace, xurl, and hyperref.
The tested versions are Pandoc 3.6.3 and MiKTeX-XeTeX 4.18.
Extract the source ZIP into an empty directory and run:

~~~text
python build_paper_b.py
python validate_paper_b_consolidated.py --output paper_b_consolidated_validation.json
~~~

Use --pandoc and --xelatex for executable paths, or --output-dir and
--build-dir to select destinations. The build compiles twice and fails
on overfull boxes, missing glyphs, or undefined references. The supplied
LaTeX can also be compiled directly twice. PDF timestamps can differ;
the rebuild check compares generated LaTeX exactly.

## Repository workflow

~~~text
python tools/build_paper_b.py
python tools/validate_paper_b_consolidated.py --output docs/theory/paper_b_consolidated_validation.json
python tools/build_paper_b.py --check
python tools/render_theorem_ledger.py --check
python -m research.juggler_sequence.branch_index --check
~~~

The builder reads docs/theory/ and tools/paper_b/. A repository build
synchronizes the review mirrors, companion PDF, and Zenodo PDF alias.
--sync repairs those mirrors without compiling. The source archive and
checksums must be regenerated after source changes; --sync alone does
not rebuild archives. Review the rendered PDF after every changed build.

## Optional symbolic review

The standalone source also includes derive_paper_b_review.py and its
result paper_b_symbolic_review.json. With SymPy installed (tested with
1.14.0), run:

~~~text
python derive_paper_b_review.py --output paper_b_symbolic_review.json
~~~

This derives leading curvature coefficients from the exact four-corner
powers. SymPy is optional for building the PDF and running the nine
standard-library exact-control modules. The fresh review and its limits
are documented in paper_b_proof_review.md.

## Evidence and licensing

The 10 September revision supplies the bounded signed-residual Fourier
extension and its variation proof, defines the parity sign before use,
clarifies shifts, and repairs subscripts and the reference link.
The aggregate validator runs nine exact modules and checks 93 equation
labels and 78 appendix references. Earlier modules retain historical
research-stage labels; those are not current theorem-status assertions.
The analytic arguments are AI-assisted written proofs. Finite scripts
check identities and exponents, not asymptotic cancellation. No surviving
gap was identified in the consolidation audit; independent mathematical
review and complete Lean verification remain outstanding.

paper_b_release_check.json records PDF preflight, the standalone rebuild,
and repository checks. Earlier reports remain historical repository
records and are not external dependencies of the manuscript.

The prepared manuscript/documentation license is CC BY 4.0:
<https://creativecommons.org/licenses/by/4.0/>. Original Python/Lua code
uses the repository's MIT license, included as LICENSE-MIT.txt.

This is a locally prepared preprint. Author approval of its text and
record fields is part of the publication decision. No upload, independent
peer-review certification, or universal termination claim is made.

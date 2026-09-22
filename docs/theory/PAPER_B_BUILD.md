# Five-Step Descent Certificates for the Juggler Map

Parity Statistics of Nested Floor Powers.

Version: 1.1.2; source edition: 23 September 2026. Author: Philippe Cochin.

The manuscript proves full five-step power-envelope certificate
density 7/8, with count error O_epsilon(N^(127/128+epsilon)).
Theorem 4.11 and Appendices A-C contain the complete OOOEE proof;
Theorem 5.4 gives the count. The four-step density 13/16 and OOEOE
estimate remain included. The stronger historical 95/96 target,
arbitrary decorations, localization, and all-depth hypotheses remain open.

## Deposit files

The record carries one file, `Five_Step_Descent_Certificates_for_the_Juggler_Map.pdf`.
`paper_b_source_package.zip` was not deposited. The source ZIP contains the complete manuscript, generated LaTeX,
build assets, all exact-control scripts, aggregate validation, fresh proof audit, metadata, and this guide. paper_b_zenodo_package.zip collects
the prepared deposit materials for convenience.

Record fields: paper_b_zenodo.json, rendered as ZENODO_FIELDS.txt.
The repository reviewer kit also contains the byte-identical PDF alias
Five_Step_Descent_Certificates_for_the_Juggler_Map.pdf and that generated
export, which both archives ship as paper_b_zenodo_fields.txt.
Submission instructions are in ZENODO_README.md. Paper B was published on
21 September 2026: version DOI 10.5281/zenodo.22864934, concept DOI
10.5281/zenodo.22864933 for all versions, recorded in paper_deposits.md.
A later revision goes up through the new-version operation of that record.

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
python tools/build_paper_b_kit.py
python tools/build_paper_b.py --check
python tools/build_paper_b_kit.py --check
python tools/render_theorem_ledger.py --check
python -m research.juggler_sequence.branch_index --check
~~~

The builder reads docs/theory/ and tools/paper_b/. A repository build
synchronizes the review mirrors, companion PDF, and Zenodo PDF alias.
--sync repairs those mirrors without compiling, but it does not rebuild
the Zenodo archives: build_paper_b_kit.py does, and its --check verifies
every archive member, both in-archive SHA256SUMS.txt files, and the kit
checksums against the files beside them. Because the release check records
the source archive's digest and the delivery bundle carries the release
check, a new edition goes --archive, then write the release check, then a
full kit build. Review the rendered PDF after every changed build.

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

The current title leads with the finite-step result. The analytic text,
Sections 2-4 and 7 and Appendices A-C, is unchanged from the 10 September
proof-audit edition; the revisions of 19 and 20 September changed the
abstract, Sections 1, 5, 6 and 8, the acknowledgments and the references
only: the identification of the word counts with the Collatz sequences
A076227, A100982 and A020914, the dropping-time convention, the attribution
of the exponential rate to Lagarias and of the d^(-3/2) power to Hikawa,
Noe's tabulation of the certificate-density increments, the closed forms of
the prefactor's jump spectrum, the list of machine-checked statements with
the declarations AxiomCheckPaperBPublished.lean audits, and the reading
status of the ResearchGate preprints. That audit supplies
the bounded signed-residual Fourier
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

Paper B was published on Zenodo on 21 September 2026. The author
page-by-page review of this edition is still outstanding, as
paper_b_release_check.json records. No independent peer-review
certification or universal termination claim is made.

## Revision of 22 September 2026

The prepared version 1.1.1 corrects the recursion's attribution to Terras
(1976, Theorem 1.14, equation (11)) and cites Winkler's arXiv:2609.22303.
The mathematical theorems, proofs and five-step density 7/8 are unchanged.
The historical statement that pages 2--42 match the deposit pixel for pixel
applies to local 1.1.0, not to this edition. The new source, PDF, validation
record and both archives are rebuilt together. No deposit is performed.

## Revision of 23 September 2026

Version 1.1.2 marks the phase-profile expansion and its limiting Fourier
relations in Section 6 as conjectural or conditional, removes a broad
priority claim, and retains the existing public references. It corrects
the logarithm of the tail growth factor and the Fourier coefficient of
log(psi) in the coboundary equation, and restores log(r) in the ladder
profile's Fourier denominator. The numbered results, their proofs,
and the five-step density 7/8 are unchanged. No private correspondence
or unpublished manuscript is cited, quoted, or included in the archives.
The deposit instructions use the canonical metadata for the prepared
version and distinguish the current package from the historical deposit.

# Five-Step Descent Certificates for the Juggler Map

Parity Statistics of Nested Floor Powers.

Version: 1.2.0; source edition: 24 September 2026. Author: Philippe Cochin.

The manuscript proves full five-step power-envelope certificate
density 7/8, with count error O_epsilon(N^(127/128+epsilon)).
Theorem 4.11 and Appendices A-C contain the complete OOOEE proof;
Theorem 5.4 gives the count. The four-step density 13/16 and OOEOE
estimate remain included. Theorem 6.3 and Appendix D prove the fair
share on almost every depth-five target fibre, by averaging. The stronger
historical 95/96 target, arbitrary decorations, localization to a
prescribed short interval, and all-depth hypotheses remain open.

## Deposit files

Versions 1.0.0, 1.1.2 and 1.2.0 each carry one file, `Five_Step_Descent_Certificates_for_the_Juggler_Map.pdf`;
`paper_deposits.md` records their DOIs, and the concept DOI 10.5281/zenodo.22864933 covers
all versions. A later revision goes up through the record's new-version operation.

The kit in `preprints/zenodo_paper_b/` has the same files as every paper's: the upload
PDF, `paper_b_sources.zip`, `ZENODO_FIELDS.txt`, `SHA256SUMS.txt`, a README and
`AFTER_ZENODO.md`. Upload the PDF and the source archive. The archive keeps repository
paths and holds every release input and output, the manifest, a generated README with
the verification commands, and its own `SHA256SUMS.txt`; an extracted copy passes
`python tools/build_paper.py B --check-release`.

## Build

Requirements: Python 3.11+, Pandoc and XeLaTeX with AMS, geometry, longtable, booktabs,
array, calc, needspace, xurl and hyperref; the tested versions are Pandoc 3.6.3 and
MiKTeX-XeTeX 4.18. From the repository root, or from an extracted source archive:

```text
python tools/build_paper.py B            # PDF, LaTeX, metadata, manifest and kit
python tools/build_paper.py B --check    # release and kit against the manifest
python tools/build_paper.py B --sync     # regenerate the kit from a current release
```

Every paper uses this one builder; the settings particular to Paper B (its files,
Lean roots, Zenodo fields and LaTeX options) are in `tools/papers/b.json`.

Paper B compiles in two passes and without the longtable-footer adjustment; both are
settings in `tools/papers/b.json`. The build fails on overfull boxes, missing glyphs or
undefined references. The exact controls run separately:

~~~text
python tools/validate_paper_b_consolidated.py --output docs/theory/paper_b_consolidated_validation.json
~~~

Review the rendered PDF after every changed build.

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

Version 1.2.0 was published on Zenodo on 24 September 2026. The author
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
Version 1.1.2 was deposited as 10.5281/zenodo.22906043; Zenodo dates it
22 September 2026.

## Revision of 24 September 2026

Version 1.2.0 adds Section 6.1 and Appendix D. Theorem 6.3 proves that,
for the words OOOEE and OOEOE, all but a power-saving proportion of the
depth-five target fibres, windows of about n^(5/32) starts, carry their
fair share 1/16. It gives no bound for a prescribed short interval. The
proof is an AI-assisted written argument; Appendix D.8 records its AI
adversarial audits, the Lean modules that check Lemma D.3 and the fibre
geometry, and the numerical controls. The 10 September proof audit does
not cover the new material. The earlier numbered results, their proofs,
and the five-step density 7/8 are unchanged. The release validator now
also requires every cited (D.n) equation to exist. Version 1.2.0 was
deposited on 24 September 2026 as 10.5281/zenodo.22946276.

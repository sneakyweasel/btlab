# Paper E: living manuscript, checks, and publication package

**The Juggler Map and the 3n±1 Maps: Exact Coding and Arithmetic Obstructions.**
Version 0.2.0, 22 September 2026. Local preprint; no deposit or DOI assigned.

Canonical source: [juggler_signed_collatz_note.md](juggler_signed_collatz_note.md).
Edit that source, never its generated reviewer copy or TeX.

## Normal update

1. Update the manuscript and the [review record](paper_e_review.md).
   Preserve theorem numbers when possible; record renamed or withdrawn statements.
2. If a formal dependency or theorem inventory changes, refresh the audit:
   python tools/check_paper_e.py --refresh
3. Run python tools/check_paper_e.py and
   python tools/generate_signed_grid_certificate.py --check.
4. Build with python tools/build_paper_e.py, then run
   python tools/build_paper_e.py --check.
5. Render the PDF and inspect every page for clipping, tables, equations,
   references, and page breaks. The build rejects overfull boxes,
   missing characters, and unresolved LaTeX references.
6. Run the paper tests and the documentation/integration gates.
   Commit the source and generated outputs together.

The builder supports --sync for refreshing exports of an already valid release,
and --allow-layout-warnings for a preview that cannot update release artifacts.
Pandoc and XeLaTeX are needed for typesetting. The normal consistency gate
uses the Python standard library and does not invoke a network service.
The numerical checker also uses the project's installed Python dependencies.
Lean is required when refreshing the proof audit.

## Outputs

- PDF: juggler_review/juggler_signed_collatz_note.pdf.
- TeX: docs/theory/cochin-juggler-signed-collatz.tex.
- Metadata: docs/theory/paper_e_zenodo.json.
- Manifest: docs/theory/paper_e_release.json.
- Validation report: docs/theory/paper_e_validation.json.
- Deposit kit: juggler_review/zenodo_paper_e/.
- Build and proof-audit logs: .build/paper_e/.

The kit contains a byte-identical PDF, upload field sheet, checksums, and
a deterministic source-and-certificate ZIP. The ZIP includes every pinned
local Lean dependency, the Lean toolchain and Lake lockfile, the full integer
certificate, generator and checker, manuscript, review record, and build tools.
Mathlib itself is restored from the pinned Lake dependency; it is not vendored.
The archive is a reproducibility supplement, not an independent verification.

The manifest hashes the transitive local Lean import closure. Editing an
underlying proof or certificate therefore stales the release even when the
manuscript is unchanged. The saved Lean report separately pins the audited
formal inputs, so rebuilding the PDF cannot silently bless a changed proof.
The integration suite automatically discovers build_paper_e.py.

## Mathematical trust boundary

- Orbit and cycle theorems: classical parity coding plus the existing
  local Lean proofs in CollatzPadic.
- Manuscript notation: PaperECompletion identifies the odd-time series
  with the residue-limit code, transfers limiting frequencies, converts
  the exact exponent bounds, and proves the direct stopping-word sums
  and finite complete prefix-tree identities.
- Signed density: actual integer trees, signed cap comparisons, closed root
  domain, well-founded induction, exact 177147-row certificate, and cutoff
  interpolation. The result has no termination conjecture hypothesis.
- Fixed-grid ceiling: both signs and every finite residue level, for precisely
  the stated rows; no upper bound on actual ancestor growth.
- Modular-return theorem: written proof importing classical fixed-function
  equidistribution. Not Lean-verified and not an actual-cycle construction.
- Mass and stopping examples: separately mapped to their compiled statements.

The combined audit selects 28 declarations and permits only propext,
Classical.choice, and Quot.sound. It builds Problems.JugglerCollatzPaper,
then executes AxiomCheckJugglerCollatzPaper.lean and checks all outputs.
The finite checker independently recomputes every certificate row, all
fifty grid phases, the small-orbit closure, examples, and exact rate
comparisons. Neither check establishes publication priority or peer review.

## Version policy

Version 0.1.0 is the first complete draft for review. Patch versions cover
editorial repairs; minor versions add results or substantial proof revisions.
A submitted or deposited file receives an immutable version: change the
version and date before replacing it with a revision. Keep published DOI
facts in the metadata; the builder preserves them and never invents them.
The SOURCE_DATE_EPOCH in the builder must agree with the edition date.

The source archive and manifest provide content-level provenance for this
draft. No manuscript commit pin is asserted before a commit containing the
complete input set exists. If a later edition prints a repository/commit
block, tools/paper_pin.py must validate it against those inputs.

## Publication and independent review

The kit prepares local files only. It does not create, reserve, submit,
or publish an external record. The author decides when and where to submit.
Use the actual first-publication date when depositing. After the first
deposit, record the version DOI, concept DOI, record URL, and file checksums
in the metadata and [deposit register](paper_deposits.md).

The [review record](paper_e_review.md) distinguishes completed local checks
from outstanding priority, statement-coverage, and external mathematical
review. A green build means the package is reproducible and internally
consistent; it is not an acceptance decision.

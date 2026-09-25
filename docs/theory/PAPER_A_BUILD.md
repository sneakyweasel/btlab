# Building and distributing Paper A

The editorial source is `juggler_finite_dynamics_note.md` in this directory.
The formalization map and reviewer packet beside it are supporting editorial
inputs. Edit those three files here. The current PDF lives in `preprints/`; its publication kit carries a generated
PDF alias. Supporting Markdown documents are kept only here.

From the repository root, with Python 3.10+, Pandoc 3.6+, and XeLaTeX installed:

```text
python tools/build_paper.py A            # PDF, LaTeX, metadata, manifest and kit
python tools/build_paper.py A --check    # release and kit against the manifest
python tools/build_paper.py A --sync     # regenerate the kit from a current release
```

Every paper uses this one builder; the settings particular to Paper A (its files,
Lean roots, Zenodo fields and LaTeX options) are in `tools/papers/a.json`.

The build generates the canonical PDF, a self-contained `cochin-juggler.tex`,
Zenodo metadata, and `paper_a_release.json`. It runs LaTeX three times and
rejects overflow, missing glyphs, and unresolved or duplicate references.
Logs are retained under `.build/paper_a/`. `--build-dir` selects another
log directory. `--pandoc` and `--xelatex` accept explicit executable paths.
`--allow-layout-warnings` creates only a draft preview, never a release.

The release manifest hashes the manuscript, supporting documents, renderer,
numeric checker, Lean toolchain, dependency lock, Paper A's transitive local
Lean imports, and cited-declaration axiom audit. Text hashes normalize line
endings so that Windows and Linux checkouts agree. It is a provenance check,
not a substitute for the mathematical verification described in the paper.

The build writes Paper A's PDF into `preprints/`, and exports the historical-named alias in `preprints/zenodo_paper_a/`.
The website carries no PDFs: Papers A–D have recorded deposits on Zenodo and the
site links the records, so `public/papers/` and `dist/papers/` are gone. The
website's prebuild still verifies the release manifest before Vite runs. On
Vercel the laboratory tree is excluded, so that verification runs on local
builds and in CI instead. A source or proof change therefore requires a fresh paper build. Use `--sync` to
repair an export only when the canonical release still matches its inputs.

Mathematical checks:

```text
python tools/check_paper_a_numeric.py --output paper_a_numeric_check.json
python -m pytest tests/research/juggler_sequence/test_paper_a_audit.py tests/research/juggler_sequence/test_paper_a_trust_boundary.py
```

The numerical checker needs `mpmath`. It screens every length through the
four reported boundaries; the descent floors remain supplied inputs. In
`formal/`, run `lake build Problems.JugglerPaper` and
`lake env lean AxiomCheckPaperA.lean`; the latter should match
`AxiomCheckPaperA.expected`. When the manuscript cites a different set of
declarations, update the audit list and regenerate its expected output.

This repository holds version 1.2.2, deposited on 25 September 2026 with its source
supplement as
[doi:10.5281/zenodo.22954947](https://doi.org/10.5281/zenodo.22954947), record
[zenodo.org/records/22954947](https://zenodo.org/records/22954947); both files are
those of commit `59362273a`. Earlier versions are 1.0.2,
[doi:10.5281/zenodo.22865237](https://doi.org/10.5281/zenodo.22865237), of
20 September 2026, 1.0.1
[doi:10.5281/zenodo.22846460](https://doi.org/10.5281/zenodo.22846460) of
19 September 2026 and 1.0.0
[doi:10.5281/zenodo.22676453](https://doi.org/10.5281/zenodo.22676453) of
9 September 2026. The concept DOI
[10.5281/zenodo.22676452](https://doi.org/10.5281/zenodo.22676452) resolves to the
latest version. A local build writes metadata only; it does not upload
a new version. Later revisions should use that record's new-version
operation. See [paper_deposits.md](paper_deposits.md). The author's ORCID is
[0009-0004-1939-3382](https://orcid.org/0009-0004-1939-3382), there is no
affiliation, and AI assistance throughout the work is disclosed. The
preprint does not claim peer review, universal termination, or exclusion
of every nontrivial cycle.

## Revision of 22 September 2026

Version 1.2.0 adds Corollary 4.11a, the Wu-Wang asymptotic exponent
5.1163051 plus epsilon, alongside Rhin's explicit bound. The logarithmic
measure remains an external theorem; its conditional Lean transfer is
recorded in the formalization map, paper barrel and dependency audit. The certified floor and
all numerical cycle exclusions remain unchanged. The earlier provenance
correction is retained. No new external deposit is performed.

## Publication kit of 23 September 2026

Version 1.2.1 changes publication preparation only. The mathematical
statements and proofs are unchanged from 1.2.0. The manuscript's provenance
pin includes the corrected metadata builder, archive packager and Lake
configuration. The Zenodo description contains only the abstract and AI
disclosure; availability and version history remain in their proper fields.

The kit in `preprints/zenodo_paper_a/` has the same files as every paper's: the upload
PDF, `paper_a_sources.zip`, `ZENODO_FIELDS.txt`, `SHA256SUMS.txt`, a README and
`AFTER_ZENODO.md`. Upload the PDF and the source archive. The archive keeps repository
paths and holds every release input and output, the manifest, a generated README with
the verification commands, and its own `SHA256SUMS.txt`; an extracted copy passes
`python tools/build_paper.py A --check-release`.

`docs/theory/paper_a_publication_check.json` records the release review and travels in the
archive. Full descent-floor replays and the laboratory probes still require the repository
and the computations described in Appendix B.

Independent mathematical review and complete Lean verification remain
outstanding and are disclosed in the manuscript and reviewer packet.

## Companion update of 25 September 2026

Version 1.2.2 updates the two sentences that describe Paper C's contagion
theorem, in the introduction and Section 6.1, and references [16] and [17],
after Paper B 1.2.0 (doi:10.5281/zenodo.22946276) and Paper C 1.3.0
(doi:10.5281/zenodo.22947659) were published. Paper C now gives the bound for
lambda at most 5/8 in Lean and for lambda at most 37/50 through Paper B's
Theorem 6.3, whose written proof has not been independently reviewed. The
1.2.1 text quoted an undeposited 22 September revision of Paper C while
citing its version 1.1.0. Paper A's statements, proofs, certified floors,
numerical period exclusions and provenance pin are unchanged. The builder
is pinned, so the PDF metadata and archive timestamps keep the 23 September
build date.

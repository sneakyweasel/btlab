# Building and distributing Paper A

The editorial source is `juggler_finite_dynamics_note.md` in this directory.
The formalization map and reviewer packet beside it are supporting editorial
inputs. Edit those three files here. Review-folder Markdown files and every
distributed Paper A PDF are generated copies.

From the repository root, with Python 3.10+, Pandoc 3.6+, and XeLaTeX installed:

```text
python tools/build_paper_a.py
python tools/build_paper_a.py --check
```

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

The build writes Paper A's PDF into `juggler_review/`, which is now its only
copy, and exports the historical-named alias in `juggler_review/zenodo_paper_a/`.
The website carries no PDFs: all three papers are deposited on Zenodo and the
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

This repository holds version 1.1.0, which is prepared and not deposited.
The record is at
[zenodo.org/records/22865237](https://zenodo.org/records/22865237); its current
version is 1.0.2,
[doi:10.5281/zenodo.22865237](https://doi.org/10.5281/zenodo.22865237), of
20 September 2026, after 1.0.1
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

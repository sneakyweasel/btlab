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

The build synchronizes Paper A into `juggler_review/`, the historical-named
PDF alias in `juggler_review/zenodo_paper_a/`, the website's `public/papers/`,
and its `dist/papers/` if a local distribution exists. The website's prebuild
checks the release and copies the canonical PDF before Vite runs. A source
or proof change therefore requires a fresh paper build. Use `--sync` to
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

The Zenodo files are a prepared preprint deposit. A build does not create or
publish an external record. The author has no affiliation and has disclosed
AI assistance throughout the work. The preprint does not claim peer review,
universal termination, or exclusion of every nontrivial cycle.

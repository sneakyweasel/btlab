# Paper A: source and verification supplement

Lower Bounds for Cycle Lengths in the Juggler Map, Philippe Cochin.
The prepared version is in `docs/theory/paper_a_zenodo.json`; the manuscript
records its edition date and the repository commit holding its pinned inputs.
This archive preserves repository paths. Extract it into an empty directory.

## Scope and evidence

The supplement contains all inputs in `docs/theory/paper_a_release.json`,
the canonical PDF and LaTeX, the formalization map and reviewer packet,
the numerical checker, Paper A's local Lean import closure, Lake configuration,
axiom audit, build assets and selected archived computational records.
`SHA256SUMS.txt` authenticates the archive contents; it does not prove the
mathematics or replace replaying the descent computations.

The numerical checker reproduces the comparisons at the four supplied floors.
It does not rerun the descent-floor searches. The full laboratory probes and
floor replays require the repository at the commit cited in Section 1.2 and
the additional artifacts and commands identified in Appendix B. Links in the
supporting documents to companion papers or laboratory dossiers refer to that
repository; those separate works are not bundled here.

No third-party dependencies, private correspondence or private manuscripts
are included. Independent mathematical review and full-paper Lean verification
remain outstanding. The manuscript distinguishes formal proofs, external
theorems, written analysis, finite computations and unproved claims.

## Rebuild the PDF

Install Python 3.10+, Pandoc 3.6+, and XeLaTeX with fontspec, AMS, geometry,
longtable, booktabs, array, calc, graphicx, fvextra, xurl and hyperref.
The tested release uses Pandoc 3.6.3 and MiKTeX-XeTeX 4.18.
From the extracted root, run:

```text
python tools/build_paper_a.py
python tools/build_paper_a.py --check
```

Executable paths may be supplied with `--pandoc` and `--xelatex`.
The build makes three LaTeX passes and rejects layout overflow, missing glyphs,
and unresolved or duplicate references. It rebuilds the PDF and its publication-kit alias
and updates the local release manifest; it performs no upload. The supplied
`docs/theory/cochin-juggler.tex` can also be compiled directly three times.
Byte identity is checked with the documented release tool versions; different
typesetting versions may produce different PDF bytes.

## Verify the numerical and formal layers

Install `mpmath`, then run from the extracted root:

```text
python tools/check_paper_a_numeric.py --output paper_a_numeric_check.json
```

For the formal layer, install elan and the Lean version recorded in
`formal/lean-toolchain`. From `formal/`, install the dependencies pinned by
`lake-manifest.json` and then run:

```text
lake exe cache get
lake build Problems.JugglerPaper
lake env lean AxiomCheckPaperA.lean
```

Compare the final command's output with `AxiomCheckPaperA.expected`.
Use the named Paper A build target: the laboratory's other default targets
are separate works and are not part of this supplement. Initial dependency
installation may need network access. The computational floors and external
transcendence estimates remain outside this Lean audit.

The outer delivery bundle carries `paper_a_publication_check.json`, the
release QA record. The source archive excludes this record to avoid a
self-referential digest. Repository kit regeneration uses
`tools/build_paper_a_kit.py` and the two-stage workflow in
`docs/theory/PAPER_A_BUILD.md`; a PDF rebuild needs neither the QA record nor
the repository's Git history.

## Licenses

The manuscript and documentation are licensed under Creative Commons
Attribution 4.0 International (CC BY 4.0), as recorded in the Zenodo metadata.
Original repository code is licensed under the MIT license in `LICENSE`.
Third-party dependencies retain their own licenses.

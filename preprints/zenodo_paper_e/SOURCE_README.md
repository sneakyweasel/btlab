# Paper E: sources and certificate

The Juggler Map and the 3n±1 Maps: Exact Coding and Arithmetic Obstructions,
Philippe Cochin. The version and deposit fields are in
`docs/theory/paper_e_zenodo.json`; the manuscript is
`docs/theory/juggler_signed_collatz_note.md`. This archive preserves
repository paths. Extract it into an empty directory.

## Contents

- The manuscript, its generated LaTeX, the build guide, the review record,
  the validation report and the release manifest, which records the SHA-256
  of every input and output (`docs/theory/paper_e_release.json`).
- The integer certificate of Theorem 5.1:
  `data/research/juggler/negative_preimage_density/grid_k12_certificate.json`,
  177147 weights, with its generator and its README.
- Every repository-local Lean module the paper's barrel
  `Problems.JugglerCollatzPaper` imports, its axiom audit, the supplementary
  audits with their expected outputs, and the Lake configuration that pins the
  Lean toolchain and Mathlib.
- The finite checker, the PDF builder with its template and layout filter,
  and one release test.
- The written notes behind the analytic lemmas of Sections 4 and C, and the
  records behind Section 7.3: the fibre-mass dossier, its follow-ups on bounded
  stopping and cross-sign pairing, and the five Lean proof maps.
- Citation records for the cited literature. They are metadata, not copies of
  the cited works.

Mathlib and other third-party dependencies are not included; Lake fetches
them. There is no private correspondence or unpublished manuscript. Links in
the notes to other laboratory records refer to the repository
[sneakyweasel/btlab](https://github.com/sneakyweasel/btlab); only the files
listed in the release manifest are bundled.

## Verify

Python 3.11 or later, standard library only. From the extracted root:

```text
python tools/check_paper_e.py
PYTHONPATH=src python tools/generate_signed_grid_certificate.py --check
```

The first command recomputes every certificate row with integers, the fifty
grid phases, the small-orbit barrier, the rational examples, the
modular-return witnesses and the exact comparisons (5.4), (5.9), (5.10) and
(6.3). It also checks the manuscript's cross-references and that the saved
Lean audit covers the declared inventory with unchanged proof inputs. The
second checks the generated Lean certificate modules against the data. On
Windows PowerShell, set `$env:PYTHONPATH = "src"` first.

For the formal proofs, install elan, then from `formal/`:

```text
lake exe cache get
lake build Problems.JugglerCollatzPaper
lake env lean AxiomCheckJugglerCollatzPaper.lean
```

The last command prints the dependencies of the 70 audited declarations; each
may use only `propext`, `Classical.choice` and `Quot.sound`.

## Rebuild the PDF

The archive omits the PDF and the publication kit, so run the build before
the check. With Pandoc and XeLaTeX installed, `python tools/build_paper_e.py`
rebuilds the PDF, the LaTeX and the kit, and `python tools/build_paper_e.py
--check` then compares every file with the release manifest. The builder fixes
`SOURCE_DATE_EPOCH`; a rebuild from this archive with Pandoc 3.6.3 and
MiKTeX-XeTeX 4.18 reproduced the kit PDF byte for byte.

## Scope

Finite checks do not prove Theorem 4.1's infinite equidistribution statement;
its Lean proof does. The divergence premise of Proposition 7.4 is open. Kernel
checking, agreement between prose and formal statements, and independent
mathematical review are separate; the last is outstanding. The grid material
adapted from M. Sharpe's repository keeps its MIT notice in the Lean sources.
The manuscript is licensed CC BY 4.0 and the software under the repository
`LICENSE`.

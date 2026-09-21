# Published preprint deposits

Version DOIs for the Zenodo preprints. These are
external records. A local `tools/build_paper_*.py` run does not create
or update them. Later revisions should use each record's new-version
operation.

| Paper | Title | Version DOI | Record |
| --- | --- | --- | --- |
| A | Lower Bounds for Cycle Lengths in the Juggler Map | [10.5281/zenodo.22676453](https://doi.org/10.5281/zenodo.22676453) | [zenodo.org/records/22676453](https://zenodo.org/records/22676453) |
| B | Five-Step Descent Certificates for the Juggler Map: Parity Statistics of Nested Floor Powers | [10.5281/zenodo.22864934](https://doi.org/10.5281/zenodo.22864934) | [zenodo.org/records/22864934](https://zenodo.org/records/22864934) |
| C | Fate Contagion and Termination Criteria for the Juggler Map | [10.5281/zenodo.22678165](https://doi.org/10.5281/zenodo.22678165) | [zenodo.org/records/22678165](https://zenodo.org/records/22678165) |

**Paper D is prepared but not deposited.** *No m-cycles of the 3n−1 map for m ≤ 58*,
version 1.0.0 of 21 September 2026, at the verification floor \(2^{51}\). The kit is
[juggler_review/zenodo_paper_d/](../../juggler_review/zenodo_paper_d/): the PDF under its
deposit name, the field sheet generated from `docs/theory/paper_d_zenodo.json`, the
checksums and a README. `python tools/build_paper_d.py` rebuilds it and `--check` verifies
it; see [PAPER_D_BUILD.md](PAPER_D_BUILD.md) for what the paper rests on. No upload has been
performed and no DOI is reserved. When it is deposited, add its row above, record the
version and concept DOIs here and in the kit's `AFTER_ZENODO.md`, and use the record's
new-version operation for any later floor.

Papers A and C are version 1.0.0 of 9 September 2026, with concept DOIs
[10.5281/zenodo.22676452](https://doi.org/10.5281/zenodo.22676452) and
[10.5281/zenodo.22678164](https://doi.org/10.5281/zenodo.22678164) for all
versions. Paper B is version
1.0.0 as well, published 21 September 2026 from the 2026-09-20-preprint
edition, with concept DOI
[10.5281/zenodo.22864933](https://doi.org/10.5281/zenodo.22864933) for all
versions. All three are resource type Publication / Preprint, license
CC BY 4.0. The Paper B record carries one file, the PDF alias of the kit
[juggler_review/zenodo_paper_b/](../../juggler_review/zenodo_paper_b/),
sha256 `4e61fcb717d5...` in that kit's `SHA256SUMS.txt`. The record
refused the session that prepared this list; a second laboratory session
with access to it read the title, version, file name and size and the
concept DOI on 21 September 2026, and the kit PDF has hashed the same
across every rebuild since the deposit, but no byte comparison against
the downloaded file has been made here.

The companion site links these DOIs from the home and claims pages. It shipped
its own copies under `web/juggler-companion/public/papers/` while Paper B had no
deposit; with all three papers on Zenodo the record is the download, and the
repository keeps one PDF per paper, in `juggler_review/`.

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
| D | No m-cycles of the 3n−1 map for m ≤ 58 | [10.5281/zenodo.22876190](https://doi.org/10.5281/zenodo.22876190) | [zenodo.org/records/22876190](https://zenodo.org/records/22876190) |

**Paper D version 1.1.0 is prepared and not deposited.** It proves the same theorem for
\(m\le61\) where 1.0.0 proved \(m\le58\), by adding the valley-count lemma; the floor is
unchanged. It goes up through the existing record's new-version operation, which keeps the
concept DOI; the kit in
[juggler_review/zenodo_paper_d/](../../juggler_review/zenodo_paper_d/) already holds its
files, so the kit PDF is no longer the deposited 1.0.0 file.

**Paper D version 1.0.0 was deposited on 21 September 2026**, at the verification floor
\(2^{51}\). Version DOI [10.5281/zenodo.22876190](https://doi.org/10.5281/zenodo.22876190), concept DOI
[10.5281/zenodo.22876189](https://doi.org/10.5281/zenodo.22876189) for all versions, resource type Publication /
Preprint, CC BY 4.0, English, open access, with the author's ORCID
[0009-0004-1939-3382](https://orcid.org/0009-0004-1939-3382) attached. The record carries one
file, `No_m_cycles_of_the_3n_minus_1_map.pdf`, 131984 bytes, md5 `c6f6f662016ca30a859bf57b0cc81793`, which is
byte-identical to the kit copy in
[juggler_review/zenodo_paper_d/](../../juggler_review/zenodo_paper_d/) and to the repository's
single PDF; the identity was checked against the record's own checksum after deposit. The
manuscript is deliberately **not** edited to carry its own DOI, so that the repository copy
stays the deposited file; the DOI enters the text at the next version. A higher floor raises
the theorem's \(m\) and is a new version through the record's new-version operation, not a
correction of this one.


**Paper B version 1.0.1 is prepared and not deposited.** It is the
2026-09-20-preprint manuscript unchanged -- `juggler_parity_discrepancy_note.md`
is byte-identical to the deposited edition, and no section, theorem, constant or
equation moved -- with the author's ORCID added to the title page. It goes up
through the existing record's new-version operation, which keeps the concept DOI.
The rebuilt artifacts are re-pinned in `paper_b_release_check.json`, whose
`front_matter_revision` field records which of that review's checks were re-run
against them and which were not.

Papers A and C are version 1.0.0 of 9 September 2026, with concept DOIs
[10.5281/zenodo.22676452](https://doi.org/10.5281/zenodo.22676452) and
[10.5281/zenodo.22678164](https://doi.org/10.5281/zenodo.22678164) for all
versions. Paper B is version
1.0.0 as well, published 21 September 2026 from the 2026-09-20-preprint
edition, with concept DOI
[10.5281/zenodo.22864933](https://doi.org/10.5281/zenodo.22864933) for all
versions. All three are resource type Publication / Preprint, license
CC BY 4.0. The Paper B record carries one file, sha256
`4e61fcb717d5...`, which was the PDF alias in the kit
[juggler_review/zenodo_paper_b/](../../juggler_review/zenodo_paper_b/)
until the ORCID revision below; that kit now holds the 1.0.1 rebuild,
sha256 `d8e8e498ef58...`, so the kit copy is no longer the deposited
file. The record refused the session that prepared this list; a second
laboratory session with access to it read the title, version, file name
and size and the concept DOI on 21 September 2026, and the kit PDF
hashed the same across every rebuild between the deposit and that
revision, but no byte comparison against the downloaded file has been
made here.

**The ORCID [0009-0004-1939-3382](https://orcid.org/0009-0004-1939-3382) is on all
four papers locally and on one live record.** Since 21 September 2026 every paper
carries it on its title page and in its prepared Zenodo metadata and generated
field sheet. Paper D's record carries it too, having been deposited with it. The
records for Papers A, B and C were deposited before it and do not. Attaching it
there is a metadata edit on each published record, which Zenodo allows without a
new version and which only the owning account can perform; a local
`tools/build_paper_*.py` run neither does it nor claims to. Until that edit is
made, the three records and this repository disagree about the creator field:

| Paper | Record | ORCID on the record |
| --- | --- | --- |
| A | [zenodo.org/records/22676453](https://zenodo.org/records/22676453) | not yet attached |
| B | [zenodo.org/records/22864934](https://zenodo.org/records/22864934) | not yet attached |
| C | [zenodo.org/records/22678165](https://zenodo.org/records/22678165) | not yet attached |
| D | [zenodo.org/records/22876190](https://zenodo.org/records/22876190) | attached at deposit |

The companion site links these DOIs from the home and claims pages. It shipped
its own copies under `web/juggler-companion/public/papers/` while Paper B had no
deposit; with all three papers on Zenodo the record is the download, and the
repository keeps one PDF per paper, in `juggler_review/`.

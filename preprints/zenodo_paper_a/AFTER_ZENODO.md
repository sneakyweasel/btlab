# Paper A Zenodo record

Four versions are published. Version 1.2.2 carries the PDF and the source and
verification supplement; the earlier versions carry the PDF alone. The 1.2.2
files are byte-identical to those of commit `59362273a`, by the md5 the Zenodo
API reported on 25 September 2026.

| Version | Published | Version DOI |
| --- | --- | --- |
| 1.2.2 | 25 September 2026 | [10.5281/zenodo.22954947](https://doi.org/10.5281/zenodo.22954947) |
| 1.0.2 | 20 September 2026 | [10.5281/zenodo.22865237](https://doi.org/10.5281/zenodo.22865237) |
| 1.0.1 | 19 September 2026 | [10.5281/zenodo.22846460](https://doi.org/10.5281/zenodo.22846460) |
| 1.0.0 | 9 September 2026 | [10.5281/zenodo.22676453](https://doi.org/10.5281/zenodo.22676453) |

- Record of the latest version: [zenodo.org/records/22954947](https://zenodo.org/records/22954947)
- Concept DOI, all versions: [10.5281/zenodo.22676452](https://doi.org/10.5281/zenodo.22676452)

The kit's source archive includes the metadata file, which now records this
deposit, so the archive here differs from the deposited one; the deposited
bytes are recoverable from the record and from commit `59362273a`.

A local `python tools/build_paper_a.py` run does not update this record.
Later revisions use the record's new-version operation, which keeps the
concept DOI. After publishing, record the returned version DOI, date and
file checksums in the canonical metadata and the
[deposit register](../../docs/theory/paper_deposits.md).

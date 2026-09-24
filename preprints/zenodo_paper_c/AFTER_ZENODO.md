# Paper C Zenodo record

Three versions are published. Each carries the PDF alone, and each PDF is
byte-identical to the repository PDF of the commit named, by the md5 the Zenodo
API reported on 25 September 2026.

| Version | Published | Version DOI | Commit |
| --- | --- | --- | --- |
| 1.3.0 | 24 September 2026 | [10.5281/zenodo.22947659](https://doi.org/10.5281/zenodo.22947659) | c43d7699f |
| 1.1.0 | 21 September 2026 | [10.5281/zenodo.22865705](https://doi.org/10.5281/zenodo.22865705) | 2cdc62495 |
| 1.0.0 | 9 September 2026 | [10.5281/zenodo.22678165](https://doi.org/10.5281/zenodo.22678165) | 1ed00a74d |

- Record of the latest version: [zenodo.org/records/22947659](https://zenodo.org/records/22947659)
- Concept DOI, all versions: [10.5281/zenodo.22678164](https://doi.org/10.5281/zenodo.22678164)

A local `python tools/build_paper_c.py` run does not update this record.
Later revisions use the record's new-version operation, which keeps the
concept DOI. After publishing a new version, verify the uploaded file
checksum and record the returned version DOI, publication date and checksum
in the [deposit register](../../docs/theory/paper_deposits.md), the metadata
and these instructions.

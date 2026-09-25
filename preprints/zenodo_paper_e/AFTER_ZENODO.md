# Paper E Zenodo record

Two versions are published. Each file is byte-identical to the repository file
of the commit named, by the md5 the Zenodo API reported on 25 September 2026.

| Version | Published | Version DOI | Files | Commit |
| --- | --- | --- | --- | --- |
| 0.8.0 | 25 September 2026 | [10.5281/zenodo.22954746](https://doi.org/10.5281/zenodo.22954746) | PDF and `Sources_and_certificate.zip` | 5a11a3b83 (PDF), 699b8203b (archive) |
| 0.7.1 | 22 September 2026 | [10.5281/zenodo.22905650](https://doi.org/10.5281/zenodo.22905650) | PDF | 5d166cee9 |

- Record of the latest version: [zenodo.org/records/22954746](https://zenodo.org/records/22954746)
- Concept DOI, all versions: [10.5281/zenodo.22905649](https://doi.org/10.5281/zenodo.22905649)

Both PDFs say in Section 1.2 that no deposit exists; they were written before the
upload. Since 0.8.0 the kit's source archive is `paper_e_sources.zip`, built by the
common laboratory builder.

A local `python tools/build_paper.py E` run does not update this record. Later
revisions use the record's new-version operation, which keeps the concept DOI.
After publishing, record the returned version DOI, date and file checksums in the
[deposit register](../../docs/theory/paper_deposits.md) and here.

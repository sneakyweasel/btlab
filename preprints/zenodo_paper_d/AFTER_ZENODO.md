# Paper D Zenodo record

**Version 1.1.0 is prepared here and not yet deposited.** It proves the same theorem for
m <= 61 where 1.0.0 proved m <= 58, by adding Lemma 6, the valley count; the floor is
unchanged at 2^51. Use the record's **new version** operation, not a fresh deposit, so the
concept DOI keeps resolving to the latest. The files to upload are the ones in this folder,
which the builder has regenerated; the PDF here is no longer the 1.0.0 file.

### After a future deposit

Verify the uploaded file checksum against the local PDF. Record the returned
version DOI and actual publication date here and in
[paper_deposits.md](../../docs/theory/paper_deposits.md), then update the
[research dossier](../../docs/problems/juggler_negative_m_cycles.md).
Review the companion site's paper card against the newly deposited edition;
it follows the concept DOI and must describe the publicly available paper.

## Version 1.0.0

Published 21 September 2026 at the verification floor 2^51.

- Version DOI: [10.5281/zenodo.22876190](https://doi.org/10.5281/zenodo.22876190)
- Concept DOI (all versions): [10.5281/zenodo.22876189](https://doi.org/10.5281/zenodo.22876189)
- Record: [zenodo.org/records/22876190](https://zenodo.org/records/22876190)
- File: `No_m_cycles_of_the_3n_minus_1_map.pdf`, 131984 bytes, md5 `c6f6f662016ca30a859bf57b0cc81793`
- ORCID attached: [0009-0004-1939-3382](https://orcid.org/0009-0004-1939-3382)

That file was byte-identical to the repository's copy when it was deposited, and the md5
above was read back from the record and compared. The repository copy has since moved on to
1.1.0, so the two no longer agree; the 1.0.0 bytes are recoverable from the record itself and
from the commit that carried them. Version 1.1.0's availability section names the 1.0.0 DOI,
which is the convention this laboratory now follows once a record exists.

A local `python tools/build_paper_d.py` run does not create or update this record. For a
later revision, including a higher verification floor, use the record's new-version
operation; the concept DOI resolves to the latest.

One field on the record is thinner than the field sheet: the relation citing Paper A
({"cites": "10.5281/zenodo.22676453"}) is not present in the record's metadata. It can be
added later as a metadata edit, which keeps the DOI.

Canonical laboratory list: [docs/theory/paper_deposits.md](../../docs/theory/paper_deposits.md).

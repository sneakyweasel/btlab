# Paper E - local publication kit

The prepared version is recorded in the
[canonical metadata](../../docs/theory/paper_e_zenodo.json), also included
in the source archive. The local ZENODO_FIELDS.txt sheet renders these
values and the deposit status for the upload form.

The builder supplies the PDF, Sources_and_certificate.zip,
ZENODO_FIELDS.txt, and SHA256SUMS.txt here. The PDF is identical
to the top-level preprint PDF. The ZIP is a deterministic snapshot
of the manuscript, proof sources, full integer certificate, tools,
license, review/build guides, and the written records behind Section 7.3.
Its top-level README.md is SOURCE_README.md from this folder.

For the preprint deposit, upload Juggler_and_signed_Collatz.pdf and
Sources_and_certificate.zip, with SHA256SUMS.txt as the integrity record.
Copy the title, creator, version, license, abstract, and related works from
ZENODO_FIELDS.txt into the upload form. Keep the preprint designation and
the stated independent-review status.

Edit docs/theory/juggler_signed_collatz_note.md and rebuild with
python tools/build_paper_e.py. Verify with --check before sharing.
Do not edit the generated files in this kit.

Version 0.8.0 was deposited on 25 September 2026 with these two files, as
[doi:10.5281/zenodo.22954746](https://doi.org/10.5281/zenodo.22954746), after 0.7.1
([doi:10.5281/zenodo.22905650](https://doi.org/10.5281/zenodo.22905650)) of
22 September. The concept DOI
[10.5281/zenodo.22905649](https://doi.org/10.5281/zenodo.22905649) resolves to the
latest version. The source archive includes the metadata file, which now
records the deposit, so the archive here differs from the deposited one, the
archive of commit `699b8203b`. Later editions use the record's versioning
operation and keep its concept DOI.

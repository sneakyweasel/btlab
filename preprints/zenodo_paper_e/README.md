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

The first deposit requires the author's decision, an actual publication
date, and the platform's returned identifiers. Do not supply a fabricated
DOI. Subsequent editions should use the existing record's versioning
operation and retain its concept DOI.

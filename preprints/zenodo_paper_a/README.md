# Paper A: prepared Zenodo preprint

This folder is generated from the canonical editorial inputs in
`docs/theory/`. The historical filename
`Lower_bounds_for_nontrivial_cycles_of_the_Juggler_map.pdf` is maintained
as a byte-identical alias of the current Paper A PDF, not an older edition.

Use `python tools/build_paper_a.py --check` from the repository root before
preparing a deposit, together with `python tools/build_paper_a_kit.py --check`.
Rebuild with `python tools/build_paper_a.py` after
editing the canonical manuscript, formalization map, or reviewer packet.
See [build instructions](../../docs/theory/PAPER_A_BUILD.md).

`ZENODO_FIELDS.txt` is generated from the manuscript's title, abstract,
version, and AI disclosure. Creator: Philippe Cochin, ORCID
[0009-0004-1939-3382](https://orcid.org/0009-0004-1939-3382), with no
affiliation. The existing CC BY 4.0 preprint license choice is retained.

The prepared version is recorded in the generated `ZENODO_FIELDS.txt`.
It is a local revision, not a new deposit. The last repository-recorded
deposit is version 1.0.2,
[doi:10.5281/zenodo.22865237](https://doi.org/10.5281/zenodo.22865237) of
20 September 2026, after 1.0.1
[doi:10.5281/zenodo.22846460](https://doi.org/10.5281/zenodo.22846460) and 1.0.0
[doi:10.5281/zenodo.22676453](https://doi.org/10.5281/zenodo.22676453). The
concept DOI
[10.5281/zenodo.22676452](https://doi.org/10.5281/zenodo.22676452) resolves to
the latest version; the record is
[zenodo.org/records/22865237](https://zenodo.org/records/22865237). A local
rebuild does not change that record.

The PDF is a preprint, not a peer-reviewed article. It establishes finite
cycle exclusions with the evidence boundaries described in the paper;
universal termination remains open. AI assistance throughout the work is
explicitly disclosed in Section 7.

For this revision, use the existing record's new-version operation.
Upload the PDF above and `paper_a_source_and_verification.zip`, with
the fields in `ZENODO_FIELDS.txt` and the actual publication date.
The source supplement contains the release-pinned inputs, manuscript and
LaTeX sources, numerical checker, Lean sources, and build instructions.
Its root README explains the required external dependencies and the
computational records that need a separate repository replay.

`paper_a_zenodo_package.zip` is the delivery bundle, not another paper.
`SHA256SUMS.txt` covers the kit, and each archive includes its own checksums.
`paper_a_publication_check.json` records the current validation and layout
review. Independent mathematical review and complete Lean verification
remain outstanding; the package does not claim either. Review the record
before publishing and record its returned version DOI after publication.

# Five-Step Descent Certificates for the Juggler Map

**Parity Statistics of Nested Floor Powers**  
Philippe Cochin | Preprint | Prepared version in paper_b_zenodo.json

## Files for the Zenodo record

The existing version 1.0.0 record carries one file:

- `Five_Step_Descent_Certificates_for_the_Juggler_Map.pdf`: the manuscript.

This package also holds `paper_b_source_package.zip`: Markdown and LaTeX
sources, build assets, exact-control scripts, symbolic review, metadata, and
licensing information. It was not included in the original deposit and
is ready to accompany the revised PDF as a reproducibility supplement.

The outer `paper_b_zenodo_package.zip` is a delivery bundle. Extract it to
obtain the record file and the accompanying preparation materials.

## Record fields

`paper_b_zenodo.json` carries the structured metadata; it is not a complete
record-creation request. The full title is the one printed above, joined by a
colon:

Five-Step Descent Certificates for the Juggler Map: Parity Statistics of Nested Floor Powers

- Resource type: Publication / Preprint.
- Creator: Cochin, Philippe. ORCID 0009-0004-1939-3382. No affiliation is
  supplied.
- Version: use the prepared version in paper_b_zenodo.json and
  paper_b_zenodo_fields.txt. Version 1.0.0 is the historical deposit.
- Language: English.
- Access: Open.
- Manuscript and documentation license: Creative Commons Attribution 4.0
  International (CC BY 4.0).
- Publication date: use the actual first-publication date of the revision;
  21 September 2026 belongs to the historical version 1.0.0.

The source archive identifies the MIT license for original Python/Lua code.
The description, keywords, and related software URL are supplied in the
metadata files. Paper B holds version DOI 10.5281/zenodo.22864934 and concept
DOI 10.5281/zenodo.22864933 for all versions; `paper_deposits.md` in the
repository records both.

The record is at <https://zenodo.org/records/22864934>. A later revision goes
up through its new-version operation, which keeps the concept DOI, rather than
as a new deposit. Official field and file guidance:
<https://help.zenodo.org/docs/deposit/describe-records/> and
<https://help.zenodo.org/docs/deposit/manage-files/>.

## Scientific scope and release checks

The paper gives five-step power-envelope descent-certificate density 7/8,
with count error O_epsilon(N^(127/128+epsilon)). This is an AI-assisted
written proof. Independent mathematical review and complete Lean
verification remain outstanding. The stronger historical 95/96 target,
general decorated estimates, localization, and all-depth hypotheses remain
open; no universal termination theorem is claimed.

The 10 September proof audit applies unchanged to every section except the
abstract and Sections 1, 5, 6 and 8, whose later paragraphs postdate it and
have had no independent audit. `paper_b_proof_review.md` records that audit
and its limitations. `paper_b_release_check.json` records the checks on this
renamed edition. `SHA256SUMS.txt` verifies the delivery files; the source
archive includes its own checksum manifest. See `PAPER_B_BUILD.md` for
rebuilding.

Paper B was published on Zenodo on 21 September 2026 as version 1.0.0. The
manuscript in this package is a prepared revision. Its Section 6 distinguishes
numerical phase-profile observations from unproved limiting statements and
uses the existing public literature for attribution. No private material is
included. The numbered results and their proofs are unchanged. Upload the
revised PDF and, if accompanying it, the source archive through the existing
record's new-version operation, which keeps the concept DOI. The delivery
bundle itself is an upload-preparation convenience, not another paper.

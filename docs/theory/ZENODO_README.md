# Five-Step Descent Certificates for the Juggler Map

**Parity Statistics of Nested Floor Powers**  
Philippe Cochin | Preprint | Prepared version in paper_b_zenodo.json

## Files for the Zenodo record

Each deposited version, 1.0.0, 1.1.2 and 1.2.0, carries one file:

- `Five_Step_Descent_Certificates_for_the_Juggler_Map.pdf`: the manuscript.

This package also holds `paper_b_source_package.zip`: Markdown and LaTeX
sources, build assets, exact-control scripts, symbolic review, metadata, and
licensing information. No deposit has included it so far; it is
ready to accompany a PDF as a reproducibility supplement.

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
- Version: use the version in paper_b_zenodo.json and
  paper_b_zenodo_fields.txt. Version 1.2.0 is deposited; a later revision
  takes a new version number.
- Language: English.
- Access: Open.
- Manuscript and documentation license: Creative Commons Attribution 4.0
  International (CC BY 4.0).
- Publication date: the actual first-publication date of each version;
  version 1.2.0 was published on 24 September 2026.

The source archive identifies the MIT license for original Python/Lua code.
The description, keywords, and related software URL are supplied in the
metadata files. Paper B's latest version DOI is 10.5281/zenodo.22946276, for
version 1.2.0, and the concept DOI 10.5281/zenodo.22864933 covers all
versions; `paper_deposits.md` in the repository records every version.

The record is at <https://zenodo.org/records/22946276>. A later revision goes
up through its new-version operation, which keeps the concept DOI, rather than
as a new deposit. Official field and file guidance:
<https://help.zenodo.org/docs/deposit/describe-records/> and
<https://help.zenodo.org/docs/deposit/manage-files/>.

## Scientific scope and release checks

The paper gives five-step power-envelope descent-certificate density 7/8,
with count error O_epsilon(N^(127/128+epsilon)). This is an AI-assisted
written proof. Independent mathematical review and complete Lean
verification remain outstanding. The stronger historical 95/96 target,
general decorated estimates, localization to a prescribed short interval, and
all-depth hypotheses remain open; no universal termination theorem is claimed.
Theorem 6.3 and Appendix D, added in 1.2.0, prove the fair share on almost every
depth-five target fibre.

The 10 September proof audit applies unchanged to every section except the
abstract and Sections 1, 5, 6 and 8, whose later paragraphs postdate it, and
Appendix D, which is new in 1.2.0; none of these has had an independent audit. `paper_b_proof_review.md` records that audit
and its limitations. `paper_b_release_check.json` records the checks on this
renamed edition. `SHA256SUMS.txt` verifies the delivery files; the source
archive includes its own checksum manifest. See `PAPER_B_BUILD.md` for
rebuilding.

Paper B was published on Zenodo as version 1.0.0 on 21 September 2026, 1.1.2
on 22 September and 1.2.0 on 24 September 2026. The manuscript in this package
is version 1.2.0, and its PDF is byte-identical to the deposited one. Its
Section 6 distinguishes numerical phase-profile observations from unproved
limiting statements and uses the existing public literature for attribution;
Section 6.1 and Appendix D add Theorem 6.3. No private material is included. A
later revision, with the source archive if it accompanies the PDF, goes up
through the record's new-version operation, which keeps the concept DOI. The delivery
bundle itself is an upload-preparation convenience, not another paper.

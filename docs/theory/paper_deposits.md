# Published preprint deposits

Version DOIs for the Zenodo preprints. These are external records. A local
`tools/build_paper_*.py` run does not create or update them. A new version goes up
through each record's new-version operation, which keeps the concept DOI.

Every record carries the author's ORCID
[0009-0004-1939-3382](https://orcid.org/0009-0004-1939-3382).

**Cite the concept DOI, not a version DOI**, whenever the intent is "this paper".
The concept DOI resolves to the latest version and cannot go stale. Papers A, C
and D each cited a sibling at a superseded version DOI until 21 September 2026,
which is what the other habit costs.

| Paper | Title | Repository | Latest deposit | Concept DOI |
| --- | --- | --- | --- | --- |
| A | Lower Bounds for Cycle Lengths in the Juggler Map | 1.2.3, not deposited | [1.2.2](https://doi.org/10.5281/zenodo.22954947) | [10.5281/zenodo.22676452](https://doi.org/10.5281/zenodo.22676452) |
| B | Five-Step Descent Certificates for the Juggler Map: Parity Statistics of Nested Floor Powers | 1.2.0, deposited | [1.2.0](https://doi.org/10.5281/zenodo.22946276) | [10.5281/zenodo.22864933](https://doi.org/10.5281/zenodo.22864933) |
| C | Fate Contagion and Termination Criteria for the Juggler Map | 1.3.0, deposited | [1.3.0](https://doi.org/10.5281/zenodo.22947659) | [10.5281/zenodo.22678164](https://doi.org/10.5281/zenodo.22678164) |
| D | No m-cycles of the 3n−1 map for m ≤ 61 | 1.1.2, not deposited | [1.1.1](https://doi.org/10.5281/zenodo.22954088) | [10.5281/zenodo.22876189](https://doi.org/10.5281/zenodo.22876189) |
| E | The Juggler Map and the 3n±1 Maps: Exact Coding and Arithmetic Obstructions | 0.8.1, not deposited | [0.8.0](https://doi.org/10.5281/zenodo.22954746) | [10.5281/zenodo.22905649](https://doi.org/10.5281/zenodo.22905649) |

Every DOI in this file was resolved against doi.org on 21 September 2026, and each
concept DOI was confirmed to return the version named beside it as the latest. Paper
B's rows for 1.1.2 and 1.2.0 were read from the Zenodo API on 24 September 2026,
where its concept record returns 1.2.0. Paper C's row for 1.3.0 was read from the
Zenodo API on 25 September 2026, where its concept record returns 1.3.0. The rows
for A 1.2.2, D 1.1.1 and both E versions were read from the Zenodo API the same day,
where each concept record returns the version named. All five papers are resource
type Publication / Preprint, CC BY 4.0, English, open access.

B and C are at their deposited versions. A, D and E are one local version ahead
(1.2.3, 1.1.2 and 0.8.1): the move to the common builder repinned A and D, and E gained
its DOIs; no statement changed. Being ahead is the normal state here: a revision
is prepared, checked and committed, and deposited only when the author decides to.
`tools/build_paper.py` prints which state a paper is in, and
`ZENODO_FIELDS.txt` says so at the top of the generated export.

## Version histories

### Paper A, Lower Bounds for Cycle Lengths in the Juggler Map

Prepared 1.2.3, 25 September 2026. Built by the common paper builder and repinned to
`efaa92cbf`; the text is otherwise 1.2.2's. Not deposited.

Published 1.2.2, 25 September 2026 (record created 08:36 UTC). Updates the
description of Paper C's contagion theorem and the references to Papers B and C to
their published versions 1.2.0 and 1.3.0, and words Section 8 so that it stays true
after deposit. Mathematical statements, proofs and the provenance pin are unchanged.
It is the first deposit with the source supplement: the PDF, 609,741 bytes, md5
`c35a72a0cf1fbfc152b0e4d7a760763d`, and `paper_a_source_and_verification.zip`,
1,537,436 bytes, md5 `2b7e9bd33f55e432c6ace56e4a8f967a`, both the files of commit
`59362273a`. The record adds the keyword "Collatz map", which the pinned builder does
not write; add it to the builder with the next version.

Prepared 1.2.1, 23 September 2026. Completes the source and verification
supplement, corrects the generated metadata description, and synchronizes
publication instructions and provenance. Mathematical statements and proofs
are unchanged from 1.2.0, including the Wu-Wang refinement and the numerical
cycle exclusions. No new deposit has been made.

Record [zenodo.org/records/22954947](https://zenodo.org/records/22954947), the latest version.

| Version | DOI | Date |
| --- | --- | --- |
| 1.2.3 | not deposited | 25 September 2026 |
| 1.2.2 | [10.5281/zenodo.22954947](https://doi.org/10.5281/zenodo.22954947) | 25 September 2026 |
| 1.2.1 | not deposited | 23 September 2026 |
| 1.2.0 | not deposited | 22 September 2026 |
| 1.1.0 | not deposited | 21 September 2026 |
| 1.0.2 | [10.5281/zenodo.22865237](https://doi.org/10.5281/zenodo.22865237) | 20 September 2026 |
| 1.0.1 | [10.5281/zenodo.22846460](https://doi.org/10.5281/zenodo.22846460) | 19 September 2026 |
| 1.0.0 | [10.5281/zenodo.22676453](https://doi.org/10.5281/zenodo.22676453) | 9 September 2026 |

**The deposited 1.0.0 carries a false provenance line, corrected in the repository
and not yet on the record.** Its Section 1.2 names commit `7802f78b` of 31 August 2026
as the state that produced the finance tables. Two files the paper points the reader
to, `exceptions_parity.json` for the 141 exceptional lengths and `budget_opt.json` for
the run-type table, were added after that commit and do not exist there, so the line
was already wrong on 9 September 2026, the day 1.0.0 was deposited. It is not rot: it
shipped that way. The prepared 1.2.2 pins `38cf9b93`, as 1.2.1 has since
23 September (it first pinned `ec0560ba`), where all 128 non-editorial
files the release manifest records as inputs are byte-identical to the versions
the paper reports, and
`tools/paper_pin.py` holds every paper to that from inside the release gate. The
correction is retained in the prepared 1.2.2, through the record's new-version
operation. The deposited PDF is not otherwise affected, because Appendix B identifies
the tables by content and both are byte-identical to the versions 1.0.0 reports.

### Paper B, Five-Step Descent Certificates for the Juggler Map

Published 1.2.0, 24 September 2026. Adds Section 6.1 and Appendix D: Theorem 6.3, the fair share on almost every depth-five target fibre, with an AI-assisted written proof that has not been independently reviewed. The earlier numbered results are unchanged. See the [release record](paper_b_release_check.json).

Published 1.1.2, dated 22 September 2026 by Zenodo (the record was created at 22:32 UTC; the edition is dated 23 September). Clarifies the conjectural status of Section 6's limiting profile and corrects three formulas there. This register listed 1.1.2 as not deposited until 24 September 2026, when the Zenodo API showed the record.

Prepared 1.1.1, 22 September 2026. Corrects the recursion attribution to Terras (1976) and Winkler's arXiv citation. Mathematical results are unchanged. Not deposited.

Record [zenodo.org/records/22946276](https://zenodo.org/records/22946276), the latest version.

| Version | DOI | Date |
| --- | --- | --- |
| 1.2.0 | [10.5281/zenodo.22946276](https://doi.org/10.5281/zenodo.22946276) | 24 September 2026 |
| 1.1.2 | [10.5281/zenodo.22906043](https://doi.org/10.5281/zenodo.22906043) | 22 September 2026 |
| 1.1.1 | not deposited | 22 September 2026 |
| 1.1.0 | not deposited | 21 September 2026 |
| 1.0.0 | [10.5281/zenodo.22864934](https://doi.org/10.5281/zenodo.22864934) | 21 September 2026 |

Version 1.0.0 was published from the edition of 20 September 2026 and carries one
file, the PDF, sha256
`4e61fcb717d51efbc3231c46117b8eded089dfd435fc91d71be22f0a36d3812d`. The record
refused the session that first prepared this list; a second laboratory session with
access to it read the title, version, file name and size and the concept DOI on
21 September 2026. On 24 September 2026 the Zenodo API reported the file's md5,
`efe486d76486193182f0bab7aa8702fe` for 295,782 bytes. That is the md5 of the PDF at
commit `8b5e596d7`, so the deposit is byte-identical to it.

Each later version also carries the PDF alone, and the API's md5 matches the
committed PDF: 1.1.2 is 298,056 bytes, md5 `ba39e6e4a7fba633616bbd5fcd81bb95`, the
PDF of commit `7c6fc3be9` (sha256
`9701a815c6082069633401c17ac2036881c8a6b7d4efd4fa3247f768d3b6030d`); 1.2.0 is
335,234 bytes, md5 `ec6aa6e0c9428f42ce28fdc490e4ab45`, the PDF of commit `f1eb45f8f`
(sha256 `e747a699ea5fbf76714cbc904afcea8fa8744c731b495af43fff57c5268dd93b`). The
1.2.0 availability section, written before the upload, still says the paper is
not deposited and names 1.0.0 as the current version.

Until 1.1.0 the repository copy was byte-identical to that deposited PDF. It is not
any more: 1.1.0 shortened the acknowledgments, added the availability section and
gave one reference its DOI, and put the author ORCID on the title page. Pages 2
to 42 of 1.1.0 are pixel-identical to the deposit; pages 1, 43 and 44 differ,
measured page by page at 100 dpi in grayscale with Poppler pdftoppm 24.04 against the
deposited file recovered from git. No page of the mathematical text moved.
`paper_b_release_check.json` records the comparison.

### Paper C, Fate Contagion and Termination Criteria for the Juggler Map

Published 1.3.0, 24 September 2026. Raises contagion to 37/50 and lowers the rate threshold to 13/50 through Paper B's Theorem 6.3 (Section 5.10), and records that the log-mass bound at 5/8, with the threshold 3/8, is now kernel-checked. See the [release manifest](paper_c_release.json).

Prepared 1.2.0, 22 September 2026. Adds the full written OOEE proof, contagion at 5/8, rate threshold 3/8, and the scale-average pressure criterion. The fully machine-checked contagion baseline was then 100/203. Not deposited.

Record [zenodo.org/records/22947659](https://zenodo.org/records/22947659), the latest version.

| Version | DOI | Date |
| --- | --- | --- |
| 1.3.0 | [10.5281/zenodo.22947659](https://doi.org/10.5281/zenodo.22947659) | 24 September 2026 |
| 1.2.0 | not deposited | 22 September 2026 |
| 1.1.1 | not deposited | 21 September 2026 |
| 1.1.0 | [10.5281/zenodo.22865705](https://doi.org/10.5281/zenodo.22865705) | 21 September 2026 |
| 1.0.0 | [10.5281/zenodo.22678165](https://doi.org/10.5281/zenodo.22678165) | 9 September 2026 |

Version 1.1.0 added Section 5.8 with its Lean layer, the corresponding rows of
Section 1.4 and Appendices A and B, the remarks of Sections 5.7, 6.3 and 7.1, and
the exponent \(\lambda_{\mathrm{ideal}}\) in the statements. 1.1.1 is editorial: the
generic acknowledgments, the availability section and two reference DOIs. It is a
patch rather than a second 1.1.0 because 1.1.0 is published, and one published
version number cannot name two different documents.

Each version carries one file, `Fate_Contagion_Juggler_Map.pdf`, and the md5 the
Zenodo API reported on 25 September 2026 is that of a committed PDF: 1.0.0 is
606,411 bytes, md5 `1bd26c1a4ca2a7c13b6585cc84958f58`, the PDF of commit
`1ed00a74d` (sha256
`168c613509670e1a8f5c31b62e86606843294799ee4e119cdc67ea3db121bd13`); 1.1.0 is
723,199 bytes, md5 `e3afd29244de03089be9bcc13b3a2597`, the PDF of commit
`2cdc62495` (sha256
`4d1d2f7f1f75e987cae98de02380f0d533607f414907b5a0e4e7a12a007298db`); 1.3.0 is
787,194 bytes, md5 `ad66599493a9d78215aac4e1513d73ca`, the PDF of commit
`c43d7699f` (sha256
`3b969e59fc33f5b5aa499557bf02a316a09735a9ed0b7b628804c871309d48cb`). The 1.3.0
availability section names 1.1.0 and 1.0.0 as the earlier versions and stays
accurate after the deposit. The deposited 1.3.0 description omits the use-of-AI
paragraph that closes `ZENODO_FIELDS.txt`, and the 1.1.0 description has none;
the 1.3.0 PDF carries that statement in its acknowledgments.

### Paper D, No m-cycles of the 3n−1 map for m ≤ 61

Record [zenodo.org/records/22954088](https://zenodo.org/records/22954088), the latest version.

| Version | DOI | Date |
| --- | --- | --- |
| 1.1.2 | not deposited | 25 September 2026 |
| 1.1.1 | [10.5281/zenodo.22954088](https://doi.org/10.5281/zenodo.22954088) | 25 September 2026 |
| 1.1.0 | not deposited | 21 September 2026 |
| 1.0.0 | [10.5281/zenodo.22876190](https://doi.org/10.5281/zenodo.22876190) | 21 September 2026 |

Prepared 1.1.2, 25 September 2026: built by the common paper builder and repinned to
`efaa92cbf`; the text is otherwise 1.1.1's. Not deposited.

Version 1.0.0 proved the theorem for \(m\le58\) at the verification floor
\(2^{51}\); 1.1.0 adds the valley-count lemma as Lemma 6 and reaches \(m\le61\) at
the same floor; 1.1.1 corrects its wording and precision, with the theorem and tables
unchanged, and was published on 25 September 2026 (record created 07:49 UTC) as one
file, 141,714 bytes, md5 `b0c53ad122a2c25ebb3c336e0a0378e3`, the PDF of commit
`e098e639d`. The record of 1.0.0 carries one file,
`No_m_cycles_of_the_3n_minus_1_map.pdf`, 131984 bytes, md5
`c6f6f662016ca30a859bf57b0cc81793`, whose identity was checked against the record's
own checksum after deposit.

While the repository copy was that deposited file, the manuscript deliberately did
not carry its own DOI, so that the copy stayed byte-identical to the deposit. That
identity ended with 1.1.0, and the DOIs entered the text there, as planned. A higher
floor raises the theorem's \(m\) and is a new version through the record's
new-version operation, not a correction.

### Paper E, The Juggler Map and the 3n±1 Maps

Prepared 0.8.1, 25 September 2026: gives its DOIs and the common build commands; no
statement changed. Not deposited.

Published 0.8.0, 25 September 2026 (record created 08:24 UTC):
`Juggler_and_signed_Collatz.pdf`, 180,942 bytes, md5
`dd852032e49425d6ae39ba9c12d88b56`, the PDF of commit `5a11a3b83`, and
`Sources_and_certificate.zip`, 2,754,843 bytes, md5
`c261b8ca3f8741ee7ff21dd0143d9846`, the archive of commit `699b8203b`. Version 0.7.1
was published on 22 September 2026 as one file, 165,575 bytes, md5
`49a5eda7861d2b250d13cddb9a8c923e`, the PDF of commit `5d166cee9`; this register
listed Paper E as undeposited until 25 September 2026. Both PDFs' Section 1.2 and
availability section, written before upload, say no deposit exists. The
[build guide](PAPER_E_BUILD.md) and [review record](paper_e_review.md) describe
its quantitative formalization and provenance.

Record [zenodo.org/records/22954746](https://zenodo.org/records/22954746), the latest
version; concept DOI [10.5281/zenodo.22905649](https://doi.org/10.5281/zenodo.22905649).

| Version | DOI | Date |
| --- | --- | --- |
| 0.8.1 | not deposited | 25 September 2026 |
| 0.8.0 | [10.5281/zenodo.22954746](https://doi.org/10.5281/zenodo.22954746) | 25 September 2026 |
| 0.7.1 | [10.5281/zenodo.22905650](https://doi.org/10.5281/zenodo.22905650) | 22 September 2026 |

Version 0.8.0, 25 September 2026: adds Section 7.3, the signed Collatz
fibre results (finite-weight obstruction and two ancestor-mass criteria, all
kernel-checked, with an open divergence premise), and Remark 5.5's exponent
423/500 from the existing certificate.

Version 0.6.0, 22 September 2026: adds the written effective OOE theorem
and complete quantitative appendix. The selected 49-declaration Lean
audit still covers the qualitative results; full quantitative verification
and independent review are outstanding. No deposit has been made.

Version 0.5.0, 22 September 2026: exact counting and prescribed-residue
corollaries, with complete Lean proofs. No deposit has been made.

Version 0.4.0, 22 September 2026: completes Theorem 4.1 in Lean, including
its analytic box-recurrence input. No deposit has been made.

Version 0.3.0, 22 September 2026: Theorem 4.1's exact construction and
denominator arithmetic are formalized. The infinitude assembly requires
BoxRecurrence, which remains unproved in Lean. No deposit has been made.

Version 0.2.0, 22 September 2026: six additional audited Lean statements
close the manuscript's series, frequency, exponent, and word-sum notation
gaps. Theorem 4.1 remains written. No deposit has been made.

Version 0.1.0, 22 September 2026: first living manuscript, prepared locally.
No external record, publication date, or DOI has been assigned.
The [build guide](PAPER_E_BUILD.md) and [review record](paper_e_review.md)
describe updates, proof boundaries, and outstanding independent review.
The local kit includes the PDF, source-and-certificate archive, upload
fields, and checksums. A build does not submit or publish it.

## Companion site

The companion site links these DOIs from the home and claims pages. It shipped its
own copies under `web/juggler-companion/public/papers/` while Paper B had no
deposit; with all four papers on Zenodo the record is the download, and the
repository keeps one PDF per paper, in `preprints/`.

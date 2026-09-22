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
| A | Lower Bounds for Cycle Lengths in the Juggler Map | 1.2.0, not deposited | [1.0.2](https://doi.org/10.5281/zenodo.22865237) | [10.5281/zenodo.22676452](https://doi.org/10.5281/zenodo.22676452) |
| B | Five-Step Descent Certificates for the Juggler Map: Parity Statistics of Nested Floor Powers | 1.1.1, not deposited | [1.0.0](https://doi.org/10.5281/zenodo.22864934) | [10.5281/zenodo.22864933](https://doi.org/10.5281/zenodo.22864933) |
| C | Fate Contagion and Termination Criteria for the Juggler Map | 1.2.0, not deposited | [1.1.0](https://doi.org/10.5281/zenodo.22865705) | [10.5281/zenodo.22678164](https://doi.org/10.5281/zenodo.22678164) |
| D | No m-cycles of the 3n−1 map for m ≤ 61 | 1.1.0, not deposited | [1.0.0](https://doi.org/10.5281/zenodo.22876190) | [10.5281/zenodo.22876189](https://doi.org/10.5281/zenodo.22876189) |
| E | The Juggler Map and the 3n±1 Maps: Exact Coding and Arithmetic Obstructions | 0.6.0, local preprint | None | Not assigned |

Every DOI in this file was resolved against doi.org on 21 September 2026, and each
concept DOI was confirmed to return the version named beside it as the latest. All
four papers are resource type Publication / Preprint, CC BY 4.0, English, open
access.

The repository is ahead of every record. That is the normal state here: a revision
is prepared, checked and committed, and deposited only when the author decides to.
`tools/build_paper_*.py` prints which state a paper is in, and
`ZENODO_FIELDS.txt` says so at the top of the generated export.

## Version histories

### Paper A, Lower Bounds for Cycle Lengths in the Juggler Map

Prepared 1.2.0, 22 September 2026. Adds the Wu-Wang asymptotic refinement, retaining Rhin's explicit bound and the provenance correction. Numerical cycle exclusions are unchanged. No new deposit has been made.

Record [zenodo.org/records/22865237](https://zenodo.org/records/22865237).

| Version | DOI | Date |
| --- | --- | --- |
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
shipped that way. The prepared 1.2.0 now pins `07482692`, where all 126 files the release
manifest records as inputs are byte-identical to the versions the paper reports, and
`tools/paper_pin.py` holds every paper to that from inside the release gate. The
correction is retained in the prepared 1.2.0, through the record's new-version
operation. The deposited PDF is not otherwise affected, because Appendix B identifies
the tables by content and both are byte-identical to the versions 1.0.0 reports.

### Paper B, Five-Step Descent Certificates for the Juggler Map

Prepared 1.1.1, 22 September 2026. Corrects the recursion attribution to Terras (1976) and Winkler's arXiv citation. Mathematical results are unchanged. No new deposit has been made.

Record [zenodo.org/records/22864934](https://zenodo.org/records/22864934).

| Version | DOI | Date |
| --- | --- | --- |
| 1.1.1 | not deposited | 22 September 2026 |
| 1.1.0 | not deposited | 21 September 2026 |
| 1.0.0 | [10.5281/zenodo.22864934](https://doi.org/10.5281/zenodo.22864934) | 21 September 2026 |

Version 1.0.0 was published from the edition of 20 September 2026 and carries one
file, the PDF, sha256
`4e61fcb717d51efbc3231c46117b8eded089dfd435fc91d71be22f0a36d3812d`. The record
refused the session that first prepared this list; a second laboratory session with
access to it read the title, version, file name and size and the concept DOI on
21 September 2026. No byte comparison against the downloaded file has been made here.

Until 1.1.0 the repository copy was byte-identical to that deposited PDF. It is not
any more: 1.1.0 shortened the acknowledgments, added the availability section and
gave one reference its DOI, and put the author ORCID on the title page. Pages 2
to 42 of 1.1.0 are pixel-identical to the deposit; pages 1, 43 and 44 differ,
measured page by page at 100 dpi in grayscale with Poppler pdftoppm 24.04 against the
deposited file recovered from git. No page of the mathematical text moved.
`paper_b_release_check.json` records the comparison.

### Paper C, Fate Contagion and Termination Criteria for the Juggler Map

Prepared 1.2.0, 22 September 2026. Adds the full written OOEE proof, contagion at 5/8, rate threshold 3/8, and the scale-average pressure criterion. The fully machine-checked contagion baseline remains 100/203. No new deposit has been made.

Record [zenodo.org/records/22865705](https://zenodo.org/records/22865705).

| Version | DOI | Date |
| --- | --- | --- |
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

### Paper D, No m-cycles of the 3n−1 map for m ≤ 61

Record [zenodo.org/records/22876190](https://zenodo.org/records/22876190).

| Version | DOI | Date |
| --- | --- | --- |
| 1.1.0 | not deposited | 21 September 2026 |
| 1.0.0 | [10.5281/zenodo.22876190](https://doi.org/10.5281/zenodo.22876190) | 21 September 2026 |

Version 1.0.0 proved the theorem for \(m\le58\) at the verification floor
\(2^{51}\); 1.1.0 adds the valley-count lemma as Lemma 6 and reaches \(m\le61\) at
the same floor. The record carries one file,
`No_m_cycles_of_the_3n_minus_1_map.pdf`, 131984 bytes, md5
`c6f6f662016ca30a859bf57b0cc81793`, whose identity was checked against the record's
own checksum after deposit.

While the repository copy was that deposited file, the manuscript deliberately did
not carry its own DOI, so that the copy stayed byte-identical to the deposit. That
identity ended with 1.1.0, and the DOIs entered the text there, as planned. A higher
floor raises the theorem's \(m\) and is a new version through the record's
new-version operation, not a correction.

### Paper E, The Juggler Map and the 3n±1 Maps

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
repository keeps one PDF per paper, in `juggler_review/`.

# Five-Step Descent Certificates for the Juggler Map

Parity Statistics of Nested Floor Powers. The prepared version and deposit
status are recorded in ZENODO_FIELDS.txt, generated from the canonical
metadata. The local kit is ready for a preprint revision; publication is a
separate action.

This folder is generated from the canonical editorial inputs in
`docs/theory/`. The deposit filename
`Five_Step_Descent_Certificates_for_the_Juggler_Map.pdf` is a byte-identical
alias of the current Paper B PDF, not an older edition.

Use `python tools/build_paper_b.py --check` from the repository root
before preparing a deposit. Rebuild with `python tools/build_paper_b.py`
after editing the canonical manuscript, then `python
tools/build_paper_b_kit.py` to regenerate the archives and checksums
in this folder; `--sync` repairs the generated metadata and the PDF alias
when the canonical PDF is already current, and does not touch the
archives. See
[build instructions](../../docs/theory/PAPER_B_BUILD.md).

`ZENODO_FIELDS.txt` is generated from `docs/theory/paper_b_zenodo.json`.
Creator: Philippe Cochin, with no affiliation. License CC BY 4.0.
Published 21 September 2026 as Zenodo record
[22864934](https://zenodo.org/records/22864934), version 1.0.0, one file,
the PDF; version DOI
[10.5281/zenodo.22864934](https://doi.org/10.5281/zenodo.22864934), concept DOI
[10.5281/zenodo.22864933](https://doi.org/10.5281/zenodo.22864933) for all versions.
The author's ORCID is
[0009-0004-1939-3382](https://orcid.org/0009-0004-1939-3382).

The PDF is a preprint proving full five-step power-envelope
certificate density 7/8, with count error O_epsilon(N^(127/128+epsilon)).
The OOOEE proof is complete within Theorem 4.11 and Appendices A-C.
The 10 September proof audit adds the bounded signed-residual Fourier
extension and verifies its variation hypotheses; it covers every section
except the abstract and Sections 1, 5, 6 and 8, whose later paragraphs
postdate it. Version 1.1.2 clarified the conjectural phase-profile
discussion and its attribution, and corrected three formula errors there.
Version 1.2.0 adds Section 6.1 and Appendix D, Theorem 6.3: the fair share
on almost every depth-five target fibre, with an AI-assisted proof that
the 10 September audit does not cover. The earlier numbered results and
their proofs are unchanged. Page-by-page
comparisons recorded for earlier editions do not describe this PDF;
paper_b_release_check.json records the current layout and file checks.
See the
[fresh proof audit](../../docs/theory/paper_b_proof_review.md).
All-depth hypotheses, arbitrary decorated estimates, and localization
to a prescribed short interval remain open. AI assistance is disclosed; independent mathematical
review and complete Lean verification remain outstanding.

The delivery bundle `paper_b_zenodo_package.zip` contains the PDF, source
archive, metadata, instructions, and release checks. See the
[submission instructions](../../docs/theory/ZENODO_README.md).
The record exists; a later revision uses its new-version operation
rather than a new deposit. The DOIs are recorded in
[paper_deposits.md](../../docs/theory/paper_deposits.md) and in
[AFTER_ZENODO.md](AFTER_ZENODO.md).

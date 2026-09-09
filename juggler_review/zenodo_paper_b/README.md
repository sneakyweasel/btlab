# Paper B: prepared Zenodo preprint

This folder is generated from the canonical editorial inputs in
`docs/theory/`. The deposit filename
`Parity_Statistics_of_Nested_Floor_Powers.pdf` is a byte-identical
alias of the current Paper B PDF, not an older edition.

Use `python tools/build_paper_b.py --check` from the repository root
before preparing a deposit. Rebuild with `python tools/build_paper_b.py`
after editing the canonical manuscript; `--sync` repairs the review
copies and this kit when the canonical PDF is already current. See
[build instructions](../../docs/theory/PAPER_B_BUILD.md).

`ZENODO_FIELDS.txt` is generated from `docs/theory/paper_b_zenodo.json`.
Creator: Philippe Cochin, with no affiliation. The prepared license is
CC BY 4.0. Use the actual date this version first becomes public as the
publication date. No DOI has been reserved, and no external record has
been created.

The PDF is a 37-page preprint proving full five-step power-envelope
certificate density 7/8, with count error O_epsilon(N^(127/128+epsilon)).
The OOOEE proof is complete within Theorem 4.11 and Appendices A-C.
The 10 September proof audit adds the bounded signed-residual Fourier
extension and verifies its variation hypotheses. See the
[fresh proof audit](../../docs/theory/paper_b_proof_review.md).
All-depth hypotheses, arbitrary decorated estimates, and localization
remain open. AI assistance is disclosed; independent mathematical
review and complete Lean verification remain outstanding.

Start a deposit at <https://zenodo.org/uploads/new>. Upload the current
Paper B PDF and the accompanying source/verification archive when
desired; Papers A and C are separate works. Review the record before
publishing. After publication, record the version DOI in
[paper_deposits.md](../../docs/theory/paper_deposits.md).

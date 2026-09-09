> **Follow-up repair, 9 September 2026:** this report records the initial review. The current manuscript restores the four-step certificate density 13/16, repairs the OE count, and proves a basic collision-model estimate. The general kernel and five-step correlation estimates remain unproved. See [the repair report](paper_b_repair_report.md) for the current results.

# Paper B publication review

Review date: 9 September 2026.

Decision: the original manuscript is not ready for release as a proof of nested parity equidistribution. At the author's request, a replacement **conditional preprint** has been prepared. Its title is *Parity Statistics of Nested Floor Powers: Conditional Descent Results for the Juggler Map*.

## Mathematical changes

The replacement retains exact proofs of the power envelope, branch indicators, minimal certificate words, and elementary floor identities. It retains the classical single-floor parity estimate and its unconditional certificate density of 3/4. It gives explicit correlation hypotheses, a sufficient mixed Fourier criterion, proofs of the conditional densities 13/16 and 7/8, and the fixed-depth implication to density-one finite certificates. The proof takes the limit in the size of the starting interval before the limit in depth.

The deterministic kernel bound, its short-interval extension, and the original effective-threshold claim are no longer presented as theorems. No proof of universal termination, or density-one arrival at 1, is claimed. The revision does not assert that the removed analytic conclusions are false; it records that the draft's proofs do not establish them.

The old working draft contains about 50,700 whitespace-separated words and mathematical tokens, including extensive audit history; the new publication manuscript is a focused nine-page conditional note. The earlier numbering is superseded. The source package and metadata use the revised title and conditional abstract.

## Principal findings in the original source

Line numbers below refer to the reviewed original Markdown snapshot, before revision.

1. **Lemma 5.2(i), Stage 5: the collision-window estimate does not account for the full gap-cell partition** (approximately lines 2865-2935; the gap-cell definition is at lines 2760-2770). The coefficient G = floor(delta_h) is constant only on intervals of length comparable to P^(1/2)/h. Stage 5 applies the smooth two-monomial test per sawtooth window, which can be much longer, while using a = (3u/2)G as though fixed on that window. The lemma invoked requires a smooth phase with fixed monomial coefficients. A proof over the common refinement, or a new global argument, is required. Merely putting the transition cost (P/M)^(1/3) on every gap cell can consume the saving: the resulting scale is h^(2/3)u^(-1/3)P^(13/12), before taking the trivial bound. The existing exponent checks do not justify omitting those pieces. This is a proof gap affecting the route to the kernel bound and the depth-four/five claims.

2. **Theorem 5.5: a global transition-set estimate is treated as proportional to the interval length** (lines 4256-4387, with the original global estimate around lines 4199-4210). Step 5b bounds a transition set over the whole dyadic block by O(P^(89/96)). The localization proof classifies costs as proportional or a unit, but this global length bound does not imply O(Y P^(-7/96)) on every interval of length Y. A short interval can lie wholly inside a transition component. The valid general restriction is min(Y, O(P^(89/96))). A local sublevel estimate is missing, so the claimed threshold Y >= P^(29/48+delta) is not established by this bookkeeping. This observation does not refute cancellation of the actual Juggler kernel.

3. **Theorem 6.1, Step D uses a frequency domain wider than Lemma 5.2(ii)** (around lines 4572-4584 versus 2480-2490). The former adds frequencies ±j/2, which can be half-integers, to coefficients governed by a lemma explicitly stated for integer q_d. Extending the lemma and rechecking its constants is required. A bound on absolute magnitude alone does not establish membership in the stated coefficient class.

4. **Some lower-depth arguments need repairs even before the main kernel** (Proposition 4.5, lines 1355-1375). Its displayed truncation of size P^(1/24) produces a P/J cost of P^(23/24), not the claimed P^(7/8). A different truncation and a complete recheck could repair this argument, but the printed proof does not do so. The replacement makes only the independently rederived single-floor estimate unconditional.

5. **Effective constants are not certified by arithmetic checks alone** (Lemma 3.3, lines 486-493; Lemma 3.10, lines 1000-1047; Appendix A, lines 6815 onward). Lemma 3.3 is stated with an implicit constant depending on the curvature ratio. Later displayed numerical coefficients are not obtained simply by dropping that constant. Appendix A also says all 38 rows are proved while explaining that its Lean file covers 31 rows. Its binding rational witness is near 4.0e13, not the advertised 3.6e13. The replacement does not reuse the threshold or present the analytic arguments as Lean-verified.

6. **The distributed PDF was stale.** The original PDF has 31 pages and a title-page date of 2 September 2026. The reviewed Markdown has a 4 September header and contains later audit changes, including the 3.6e13 threshold and localized-kernel discussion. A fresh build was necessary. Section headings and theorem numbers in the original also followed different numbering schemes.

7. **The original AI disclosure and audit history overstated the evidence.** The source repeatedly describes the analytic arguments as human proofs while recording extensive model-assisted development. The replacement describes the assistance in proof development, drafting, code, and review, and does not treat AI review or script checks as independent validation. Speculative method discussions, repeated errata, threshold anecdotes, and unused references have been removed from the publication text.

## Verification

The earlier targeted audit run completed with 346 passing tests and one environment failure. The failing check attempted to run Lean: the sandbox first lacked ELAN_HOME; setting it exposed a Git ownership failure for the installed Mathlib checkout. That is not evidence of a mathematical failure, and no fresh Lean certification is claimed. The passing tests concern the former draft's arithmetic and source consistency, not the missing analytic steps.

After repository integration, the required integration and theorem-ledger suite completed with **119 passed and 11 skipped**. The expanded historical audit completed with **855 passed, one failed, and one deselected**. The failure is the existing Paper A notation test `test_d_is_the_depth_and_nothing_else`: it expects two standalone uses of `d` but finds none in Paper A. The saved pre-edit test reproduces the same failure; its function and the symbol-scanning implementation were not changed by this revision. The deselected test is the Lean-launch check whose environment failure is described above. No assertions were weakened to make these outcomes disappear.

The new standalone validation script uses Python integer and rational arithmetic. It passes 16,000 power-envelope checks, 6,231 branch-indicator checks, 3,150 factorization/inequality checks, and 10,201 carry checks. It exhaustively enumerates the minimal contracting words through length five and records auxiliary word-survivor counts through depth sixteen. The fractions 13/16 and 7/8 are checked as **conditional fair-share sums**, not measured or proved unconditional orbit densities.

The new PDF was built from the replacement Markdown with Pandoc and XeLaTeX, checked for compiler warnings and missing glyphs, and visually reviewed on all pages. The package includes the complete LaTeX source, the Markdown source, build assets, validation code, validation results, and checksums. No Zenodo record has been created or published.

The standalone package was rebuilt using its own source discovery and bundled layout assets. Its generated LaTeX matches the delivered LaTeX byte for byte. All PDF fonts are embedded; the PDF title and author match the prepared metadata. The nine final pages have no observed clipping, overlap, or broken tables. These release checks are recorded in `paper_b_release_check.json`.

## Zenodo fields and downstream implications

The prepared metadata identifies a publication/preprint by Philippe Cochin and makes the conditional status explicit in the title and abstract. The proposed manuscript license is CC BY 4.0, matching the companion preprint's prepared metadata; it can be changed before deposit. Use the actual first-publication date for the publication-date field. No DOI, ORCID, affiliation, funding award, or peer-review status has been invented.

Zenodo's [record-description guide](https://help.zenodo.org/docs/deposit/describe-records/) documents these fields, including DOI reservation, resource type, creators, description, and licensing. The [license guide](https://help.zenodo.org/docs/deposit/describe-records/licenses/) explains the record's reuse-license field. These were consulted for deposit preparation; uploading was outside this request.

The canonical manuscript, reviewer mirrors, local PDF copies, main reading guides, and relevant theorem-ledger entries have been updated to the conditional status. The original 4 September Markdown is preserved byte for byte under the dated filename `juggler_parity_discrepancy_note_2026_09_04.md`. Historical source-based audits now read that snapshot, and their ledger carries a supersession notice. Unrelated working-tree changes have been preserved.

Historical research notes and companion manuscripts still cite the superseded unconditional Paper B claims. They must not be treated as independent proofs of those claims. In particular, Paper C references Paper B in its introduction and later comparisons. Its results require a separate dependency review before deciding which remain unconditional. This review does not withdraw or validate those companion results wholesale.

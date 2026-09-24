# Literature registry

Structured metadata lives under `literature/`. The Python API is
`research.literature`.

Each record has:

- title, authors, year
- DOI / arXiv / URL
- problem area
- relevant concepts
- project relationship (`known`, `reproduced`, `extended`,
  `independent`, `refuted`)
- status and notes

When recovering or consulting a source, add a `consultation` object with
`checked_on`, `level`, `scope`, and `remaining`. Use `selected_sections`,
`abstract_and_intro`, or `preview_only` for partial reading. Record the exact
version and theorem/page scope; a publication's status is separate from how
much of it we have read. A located PDF, publisher abstract or book preview is
not a checked proof. Keep copyrighted source copies outside tracked content.

## Reading arXiv through alphaXiv

Claude sessions on the owner's account have the alphaXiv connector, a hosted
claude.ai connector rather than a server in `.mcp.json`; Codex and Cursor do not
see it. Every query leaves the machine. Search only for published material, and
never paste unpublished results, draft manuscripts or correspondence into it.

- `answer_pdf_queries` takes an arXiv id, URL or title and returns the ranked
  pages of the PDF with the version stamp; batch every question for one paper
  into one call. Cite and record from these pages.
- `get_paper_content` returns an AI-generated report by default. It is a
  summary, not the paper: pass `fullText=true` before quoting or recording a
  statement from it.
- `discover_papers` ranks candidates for a topic, two searches per message. It
  matches words, not mathematics: "juggler sequence" returns juggling-pattern
  (siteswap) papers. A miss establishes nothing about novelty; use OEIS
  cross-references and the registry for prior art.
- The researcher tools look up authors and coauthors. Folder, library and
  follow tools change the owner's alphaXiv account; ask before using them.

A paper read this way gets a registry record with a `consultation` object that
names the arXiv version and the pages read, as for any other source.

Checked 24 September 2026: `answer_pdf_queries` on 2107.11160 returned all 17
pages of v4 (20 Oct 2021), agreeing with the
`eliahou-fromentin-simonetto-2021-falling-time` record read from a local copy.

## Comparison records

Current comparison records:

- [Recovered Collatz/Juggler literature gaps and remaining access work](../research/literature_gap_recovery.md)
- [Four-coordinate literature comparison](../literature_comparison.md)
- [Balanced ternary versus Collatz literature](../balanced_ternary_vs_collatz_literature.md)
- [Cycle literature comparison](../cycle_literature_comparison.md)
- [Cycle literature replication](../cycle_literature_replication.md)
- [Paper B prior art and external names](../theory/paper_b_prior_art_and_names.md)

The registry exists so the project does not rediscover known results and
so preprint claims are not adopted as theorems.
Removed independent research is available through [Git history](../history.md).

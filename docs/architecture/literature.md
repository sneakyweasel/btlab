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

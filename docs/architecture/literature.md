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

Existing comparison documents are not deleted. They are indexed from
this registry:

- [Rewrite-calculus positioning table](https://github.com/sneakyweasel/btlab/blob/f038c8526134cdaabd10857b23a87520c7cebc4f/docs/theory/rewrite_calculus.md#position-after-the-prior-art-audit)
- [Rewrite-calculus dossier](https://github.com/sneakyweasel/btlab/blob/f038c8526134cdaabd10857b23a87520c7cebc4f/docs/problems/rewrite_calculus.md)
- [Rewrite-calculus prior-art audit](https://github.com/sneakyweasel/btlab/blob/f038c8526134cdaabd10857b23a87520c7cebc4f/docs/theory/rewrite_calculus_prior_art.md)
- [Four-coordinate literature comparison](../literature_comparison.md)
- [Balanced ternary versus Collatz literature](../balanced_ternary_vs_collatz_literature.md)
- [Cerdá comparison](https://github.com/sneakyweasel/btlab/blob/f038c8526134cdaabd10857b23a87520c7cebc4f/docs/cerda_comparison.md)
- [Cycle literature comparison](../cycle_literature_comparison.md)
- [Cycle literature replication](../cycle_literature_replication.md)
- [Paper B prior art and external names](../theory/paper_b_prior_art_and_names.md)

The registry exists so the project does not rediscover known results and
so preprint claims are not adopted as theorems.

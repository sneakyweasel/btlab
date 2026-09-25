# Paper D: Zenodo publication kit

**No m-cycles of the 3n−1 map for m ≤ 61.**

Every laboratory paper's kit has these files, all generated except this README and
`AFTER_ZENODO.md`:

- `No_m_cycles_of_the_3n_minus_1_map.pdf`: the paper, byte-identical to
  `preprints/collatz_3n_minus_1_m_cycles_note.pdf`. Upload it.
- `paper_d_sources.zip`: the sources and verification files, with a README
  that gives the checks and the rebuild. Upload it.
- `ZENODO_FIELDS.txt`: the upload form's fields, including the plain-text description
  and the related works. Its first lines say whether this version is deposited.
- `SHA256SUMS.txt`: checksums of the kit.
- `AFTER_ZENODO.md`: the published versions and their DOIs.

From the repository root:

```text
python tools/build_paper.py D            # rebuild the paper and this kit
python tools/build_paper.py D --check    # verify the paper and this kit
```

Edit `docs/theory/collatz_3n_minus_1_m_cycles_note.md` or `tools/papers/d.json`, never a
generated file here. The [build guide](../../docs/theory/PAPER_D_BUILD.md) gives the
paper's trust boundaries and review status. A new version goes up through the
existing record's new-version operation, which keeps the concept DOI.

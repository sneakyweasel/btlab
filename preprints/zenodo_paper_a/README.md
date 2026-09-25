# Paper A: Zenodo publication kit

**Lower Bounds for Cycle Lengths in the Juggler Map.**

Every laboratory paper's kit has these files, all generated except this README and
`AFTER_ZENODO.md`:

- `Lower_bounds_for_nontrivial_cycles_of_the_Juggler_map.pdf`: the paper, byte-identical to
  `preprints/juggler_finite_dynamics_note.pdf`. Upload it.
- `paper_a_sources.zip`: the sources and verification files, with a README
  that gives the checks and the rebuild. Upload it.
- `ZENODO_FIELDS.txt`: the upload form's fields, including the plain-text description
  and the related works. Its first lines say whether this version is deposited.
- `SHA256SUMS.txt`: checksums of the kit.
- `AFTER_ZENODO.md`: the published versions and their DOIs.

From the repository root:

```text
python tools/build_paper.py A            # rebuild the paper and this kit
python tools/build_paper.py A --check    # verify the paper and this kit
```

Edit `docs/theory/juggler_finite_dynamics_note.md` or `tools/papers/a.json`, never a
generated file here. The [build guide](../../docs/theory/PAPER_A_BUILD.md) gives the
paper's trust boundaries and review status. A new version goes up through the
existing record's new-version operation, which keeps the concept DOI.

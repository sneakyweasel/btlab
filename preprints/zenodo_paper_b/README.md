# Paper B: Zenodo publication kit

**Five-Step Descent Certificates for the Juggler Map: Parity Statistics of Nested Floor Powers.**

Every laboratory paper's kit has these files, all generated except this README and
`AFTER_ZENODO.md`:

- `Five_Step_Descent_Certificates_for_the_Juggler_Map.pdf`: the paper, byte-identical to
  `preprints/juggler_parity_discrepancy_note.pdf`. Upload it.
- `paper_b_sources.zip`: the sources and verification files, with a README
  that gives the checks and the rebuild. Upload it.
- `ZENODO_FIELDS.txt`: the upload form's fields, including the plain-text description
  and the related works. Its first lines say whether this version is deposited.
- `SHA256SUMS.txt`: checksums of the kit.
- `AFTER_ZENODO.md`: the published versions and their DOIs.

From the repository root:

```text
python tools/build_paper.py B            # rebuild the paper and this kit
python tools/build_paper.py B --check    # verify the paper and this kit
```

Edit `docs/theory/juggler_parity_discrepancy_note.md` or `tools/papers/b.json`, never a
generated file here. The [build guide](../../docs/theory/PAPER_B_BUILD.md) gives the
paper's trust boundaries and review status. A new version goes up through the
existing record's new-version operation, which keeps the concept DOI.

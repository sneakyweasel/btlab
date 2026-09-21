# Paper D: Zenodo preprint kit

**No m-cycles of the 3n−1 map for m ≤ 58.** Version 1.0.0, 21 September 2026.

**Deposited.** Version DOI [10.5281/zenodo.22876190](https://doi.org/10.5281/zenodo.22876190), concept DOI
[10.5281/zenodo.22876189](https://doi.org/10.5281/zenodo.22876189), record
[zenodo.org/records/22876190](https://zenodo.org/records/22876190). The PDF here is byte-identical to the deposited
file (md5 `c6f6f662016ca30a859bf57b0cc81793`). See [AFTER_ZENODO.md](AFTER_ZENODO.md).

This folder is generated from the canonical editorial inputs in `docs/theory/`. Do not edit
anything here; edit
[collatz_3n_minus_1_m_cycles_note.md](../../docs/theory/collatz_3n_minus_1_m_cycles_note.md)
and rebuild.

```
python tools/build_paper_d.py            # rebuild everything, including this kit
python tools/build_paper_d.py --check    # verify the kit against the manifest
```

See the [build instructions](../../docs/theory/PAPER_D_BUILD.md) for what the paper rests on:
which lemmas are proved by hand, which two are machine-checked, which single input is
external (Rhin's measure), and which part is a computation of this laboratory rather than a
result from the literature (the verification floor).

## What was uploaded

| file | role |
| --- | --- |
| `No_m_cycles_of_the_3n_minus_1_map.pdf` | the preprint; a byte-identical alias of `juggler_review/collatz_3n_minus_1_m_cycles_note.pdf` |
| `ZENODO_FIELDS.txt` | the deposit form, field by field, generated from `docs/theory/paper_d_zenodo.json` |
| `SHA256SUMS.txt` | checksums of the PDF and its alias |

Resource type Publication / Preprint, license CC BY 4.0, English, open access. The
description in the field sheet is the abstract followed by the AI-assistance disclosure, as
the other three papers carry.

## What this is and is not

A preprint, not a peer-reviewed article, and not refereed. The theorem is conditional on
Rhin's effective measure for linear forms in log 2 and log 3, and on a verification floor
that is this laboratory's own computation. Neither the 3n−1 cycle question nor divergence is
settled. AI assistance throughout the work is disclosed in the manuscript.

A local build prepares metadata only; it does not create or update any external record. For a
later revision, including a higher verification floor, use the existing record's new-version
operation rather than a fresh deposit.

Canonical laboratory list of deposits: [paper_deposits.md](../../docs/theory/paper_deposits.md).
